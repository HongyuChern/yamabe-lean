import Yamabe3.Analysis.NativeHalfEndStrongCauchy
import Yamabe3.Analysis.SpectralHalfEndPotentialEquation
import Yamabe3.Analysis.HighModeCoercivityConstants

/-!
The actual inward-half-line Dirichlet-to-Neumann operator on the existing
round sphere H1 completion. Its value is minus the actual right derivative
of the already constructed Poisson field. The lower bound is derived from
the same field's ODE and tails, not assumed as boundary data.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

private def physicalAtCLM (t : ℝ) : AngularH1 →L[ℝ] AngularL2 :=
  Real.exp (-2 * t) • ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) t.toNNReal).comp
    (nativeHalfHighPotentialPoissonCLM hκ0 hκ1 V hV hV0))

private theorem physicalAtCLM_apply (b : AngularH1) (t : ℝ) :
    physicalAtCLM hκ0 hκ1 V hV hV0 t b =
      nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b t := rfl

private theorem derivative_add (b c : AngularH1) :
    nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 (b + c) 0 =
      nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b 0 +
      nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 c 0 := by
  apply (uniqueDiffOn_Ici (0 : ℝ) 0 (mem_Ici.mpr le_rfl)).eq_deriv _
    (nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 (b+c) 0 le_rfl)
  apply ((nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 b 0 le_rfl).add
    (nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 c 0 le_rfl)).congr_of_mem _ (mem_Ici.mpr le_rfl)
  intro t _
  exact map_add (physicalAtCLM hκ0 hκ1 V hV hV0 t) b c

private theorem derivative_smul (r : ℝ) (b : AngularH1) :
    nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 (r • b) 0 =
      r • nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b 0 := by
  apply (uniqueDiffOn_Ici (0 : ℝ) 0 (mem_Ici.mpr le_rfl)).eq_deriv _
    (nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 (r • b) 0 le_rfl)
  apply ((nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 b 0 le_rfl).const_smul r).congr_of_mem _ (mem_Ici.mpr le_rfl)
  intro t _
  exact map_smul (physicalAtCLM hκ0 hκ1 V hV hV0 t) r b

/-- Genuine DtN, with the normal pointing out of the positive half-line. -/
def nativeHighDtN : AngularH1 →L[ℝ] AngularL2 :=
  ({ toFun := fun b => -nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b 0
     map_add' := fun b c => by rw [derivative_add, neg_add]
     map_smul' := fun r b => by rw [derivative_smul, smul_neg]; rfl } :
    AngularH1 →ₗ[ℝ] AngularL2).mkContinuous
      (1 + (10 / 9 : ℝ) * ‖V‖ / (1 - κ)) (fun b => by
        change ‖-nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b 0‖ ≤ _
        simpa only [norm_neg, mul_zero, Real.exp_zero, one_mul] using
          (nativeHalfHighPotentialPhysical_weighted_cauchy hκ0 hκ1 V hV hV0 b 0 le_rfl).2)

@[simp] theorem nativeHighDtN_apply (b : AngularH1) :
    nativeHighDtN hκ0 hκ1 V hV hV0 b =
      -nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b 0 := rfl

private theorem physical_coordinate (b : AngularH1) (i : AngularIndex) (t : ℝ) :
    inner ℝ (angularBasis i) (nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b t) =
      Real.exp (-2 * t) * spectralHalfPotentialPoissonCLM nativeAngularRate
        (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
        (angularBasis.repr (nativeHighProjection (angularEmbedding b))) t.toNNReal i := by
  rw [nativeHalfHighPotentialPhysical, real_inner_smul_right,
    nativeHalfHighPotentialPoissonCLM_apply, ← HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.apply_symm_apply]

private theorem coordinate_zero (b : AngularH1) (i : AngularIndex)
    (hb : inner ℝ (angularBasis i) (nativeHighProjection (angularEmbedding b)) = 0) :
    inner ℝ (angularBasis i) (nativeHighDtN hκ0 hκ1 V hV hV0 b) = 0 := by
  let ev : AngularL2 →L[ℝ] ℝ := innerSL ℝ (angularBasis i)
  have hz (t : ℝ) : ev (nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b t) = 0 := by
    rw [show ev = innerSL ℝ (angularBasis i) from rfl]
    change inner ℝ (angularBasis i) _ = 0
    rw [physical_coordinate, spectralHalfPotentialPoissonCLM_coordinate_zero]
    · exact mul_zero _
    · simpa only [HilbertBasis.repr_apply_apply] using hb
  have hd := ev.hasFDerivAt.comp_hasDerivWithinAt 0
    (nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 b 0 le_rfl)
  have hc : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
      (ev (nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b 0)) (Ici 0) 0 :=
    hd.congr_of_mem (fun t _ => (hz t).symm) (mem_Ici.mpr le_rfl)
  have h := (uniqueDiffOn_Ici (0 : ℝ) 0 (mem_Ici.mpr le_rfl)).eq_deriv _ hc
    (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt
  change inner ℝ (angularBasis i) (nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b 0) = 0 at h
  simpa only [nativeHighDtN_apply, inner_neg_right, neg_eq_zero] using h

/-- DtN is diagonal in the actual angular basis. -/
def nativeHighDtNSymbol (i : AngularIndex) : ℝ :=
  inner ℝ (angularBasis i) (nativeHighDtN hκ0 hκ1 V hV hV0 (angularEnergyMode i))

theorem nativeHighDtN_coefficient (b : AngularH1) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeHighDtN hκ0 hκ1 V hV hV0 b) =
      if 6 ≤ angularEigenvalue i then
        nativeHighDtNSymbol hκ0 hκ1 V hV hV0 i * inner ℝ (angularBasis i) (angularEmbedding b)
      else 0 := by
  classical
  by_cases hi : 6 ≤ angularEigenvalue i
  · rw [if_pos hi]
    let c := inner ℝ (angularBasis i) (angularEmbedding b)
    have hz := coordinate_zero hκ0 hκ1 V hV hV0 (b - c • angularEnergyMode i) i (by
      rw [nativeHighProjection, nativeAngularProjection_coefficient, if_pos hi,
        map_sub, map_smul, angularEmbedding_energyMode, inner_sub_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq, angularBasis.orthonormal.1, one_pow, mul_one]
      exact sub_self c)
    rw [map_sub, map_smul, inner_sub_right, real_inner_smul_right] at hz
    change _ - c * nativeHighDtNSymbol hκ0 hκ1 V hV hV0 i = 0 at hz
    dsimp only [c] at hz
    nlinarith only [hz]
  · rw [if_neg hi]
    exact coordinate_zero hκ0 hκ1 V hV hV0 b i (by
      rw [nativeHighProjection, nativeAngularProjection_coefficient, if_neg hi])

/-- The actual normal lies in the same high L2 subspace. -/
theorem nativeHighDtN_high (b : AngularH1) :
    nativeHighProjection (nativeHighDtN hκ0 hκ1 V hV hV0 b) =
      nativeHighDtN hκ0 hκ1 V hV hV0 b := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighProjection, nativeAngularProjection_coefficient, nativeHighDtN_coefficient]
  split_ifs <;> rfl

/-- The true coordinate derivative satisfies the true equation, including
its coefficient with the same potential. -/
theorem nativeHalfHighPotentialPhysical_derivative_equation
    (b : AngularH1) (i : AngularIndex) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => inner ℝ (angularBasis i)
      (nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b s))
      ((nativeAngularRate i ^ 2 - V t) * inner ℝ (angularBasis i)
        (nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b t)) t := by
  let ev : AngularL2 →L[ℝ] ℝ := innerSL ℝ (angularBasis i)
  let z := fun s : ℝ => ev (nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b s)
  have hz (s : ℝ) (hs : 0 < s) : HasDerivAt z
      (ev (nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b s)) s :=
    ev.hasFDerivAt.comp_hasDerivAt s
      (nativeHalfHighPotentialPhysical_hasDerivAt hκ0 hκ1 V hV hV0 b s hs)
  have heq : (fun s : ℝ => ev (nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b s))
      =ᶠ[𝓝 t] deriv z := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hz s hs).deriv.symm
  have hfun : z = fun s : ℝ => Real.exp (-2 * s) * spectralHalfPotentialPoissonCLM
      nativeAngularRate (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
      (angularBasis.repr (nativeHighProjection (angularEmbedding b))) s.toNNReal i :=
    funext (physical_coordinate hκ0 hκ1 V hV hV0 b i)
  have h := spectralHalfPotentialPoissonCLM_physical_coordinate_equation nativeAngularRate
    (by norm_num) nativeAngularRate_lower hκ0 hκ1 V hV hV0
    (angularBasis.repr (nativeHighProjection (angularEmbedding b))) i t ht
  change HasDerivAt (deriv _) _ t at h
  rw [← hfun] at h
  exact h.congr_of_eventuallyEq heq

/-- No boundary coercivity premise: the scalar energy theorem is applied
to the actual Poisson coordinate and its actual derivative and tails. -/
theorem nativeHighDtNSymbol_lower
    (hVupper : ∀ t : ℝ, 0 ≤ t → V t ≤ 15 / 4)
    (i : AngularIndex) (hi : 6 ≤ angularEigenvalue i) :
    angularEnergyWeight i / 4 + 1 / 2 ≤ nativeHighDtNSymbol hκ0 hκ1 V hV hV0 i := by
  let b := angularEnergyMode i
  let U := nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b
  let D := nativeHalfHighPotentialPhysicalDerivative hκ0 hκ1 V hV hV0 b
  let ev : AngularL2 →L[ℝ] ℝ := innerSL ℝ (angularBasis i)
  have hUt := halfEnd_tendsto_zero_of_expTwo_bound U (‖b‖ / (1-κ))
    (fun t ht => (nativeHalfHighPotentialPhysical_weighted_cauchy hκ0 hκ1 V hV hV0 b t ht).1)
  have hDt := halfEnd_tendsto_zero_of_expTwo_bound D
    ((1 + (10/9:ℝ) * ‖V‖ / (1-κ)) * ‖b‖)
    (fun t ht => (nativeHalfHighPotentialPhysical_weighted_cauchy hκ0 hκ1 V hV hV0 b t ht).2)
  have hz0 : ev (U 0) = 1 := by
    change inner ℝ (angularBasis i) (nativeHalfHighPotentialPhysical hκ0 hκ1 V hV hV0 b 0) = 1
    rw [nativeHalfHighPotentialPhysical_zero, nativeHighEnergyProjectionCLM_embedding,
      nativeHighProjection, nativeAngularProjection_coefficient, if_pos hi]
    dsimp only [b]
    rw [angularEmbedding_energyMode, real_inner_self_eq_norm_sq, angularBasis.orthonormal.1, one_pow]
  have h := halfEnd_scalar_coercivity (fun t => ev (U t)) (fun t => ev (D t))
    (fun t => nativeAngularRate i ^ 2 - V t)
    (fun t ht => ev.hasFDerivAt.comp_hasDerivWithinAt t
      (nativeHalfHighPotentialPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 b t ht))
    (ev.continuous.comp (nativeHalfHighPotentialPhysicalDerivative_continuous hκ0 hκ1 V hV hV0 b)).continuousOn
    (continuous_const.sub V.continuous).continuousOn
    (nativeHalfHighPotentialPhysical_derivative_equation hκ0 hκ1 V hV hV0 b i)
    (Real.sqrt (angularEigenvalue i - 7/2)) (fun t ht => by
      rw [highMode_coercivity_gap_sq _ hi, nativeAngularRate_sq, max_eq_right hi]
      linarith only [hVupper t ht])
    (by simpa only [Function.comp_def, map_zero] using ev.continuous.continuousAt.tendsto.comp hUt)
    (by simpa only [Function.comp_def, map_zero] using ev.continuous.continuousAt.tendsto.comp hDt)
  rw [hz0, one_pow, mul_one, mul_one] at h
  have hgap := highMode_coercivity_gap_lower (angularEigenvalue i) hi
  change angularEnergyWeight i / 4 ≤ Real.sqrt (angularEigenvalue i - 7/2) - 1/2 at hgap
  have hd : nativeHighDtNSymbol hκ0 hκ1 V hV hV0 i = -ev (D 0) := by
    rw [nativeHighDtNSymbol, nativeHighDtN_apply, inner_neg_right]
    rfl
  rw [hd]
  linarith only [h, hgap]

#print axioms nativeHighDtN
#print axioms nativeHighDtN_coefficient
#print axioms nativeHalfHighPotentialPhysical_derivative_equation
#print axioms nativeHighDtNSymbol_lower
end Yamabe3.Analysis.Delaunay
