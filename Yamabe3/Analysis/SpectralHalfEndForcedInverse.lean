import Yamabe3.Analysis.SpectralHalfEndPotentialEquation

/-!
# A constructed forced Dirichlet inverse for the same half-end potential

The full-line inverse is the actual integrated-potential Banach fixed point.
We apply it to the actual physical even extension of the source, restrict
to nonnegative time, and subtract the already constructed same-potential
Poisson curve with the actual entrance value.  This produces the original
zero-entrance field as a continuous linear map.  Its equation, coordinate
C2 regularity and unweighted equation are proved from that construction.

The potential is bounded continuous and nonnegative, with the original
integrated majorant bound `κ < 1`.  No pointwise smallness, smooth source,
supplied inverse, or free differential equation is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff lp BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

variable {ι : Type*} (k : ι → ℝ) {k₀ κ : ℝ}
  (hk₀ : 2 < k₀) (hk : ∀ i, k₀ ≤ k i) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
  (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

private def halfEndFullPotentialCLM :
    (ℝ≥0 →ᵇ SpectralSpace ι) →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  (spectralIntegralPotentialInverseCLM k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV).comp
      halfEndPhysicalEvenExtensionCLM

/-- The actual forced zero-entrance operator, with the same potential in
both its full-line inverse and its boundary correction. -/
def spectralHalfPotentialDirichletCLM :
    (ℝ≥0 →ᵇ SpectralSpace ι) →L[ℝ] (ℝ≥0 →ᵇ SpectralSpace ι) :=
  halfEndRestrictionCLM.comp (halfEndFullPotentialCLM k hk₀ hk hκ0 hκ1 V hV) -
    (spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0).comp
      ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) 0).comp
        (halfEndFullPotentialCLM k hk₀ hk hκ0 hκ1 V hV))

/-- An explicit identity with the actual full-line fixed point. -/
theorem spectralHalfPotentialDirichletCLM_apply
    (F : ℝ≥0 →ᵇ SpectralSpace ι) (t : ℝ≥0) :
    let A := spectralIntegralPotentialInverse k (by linarith : 0 < k₀) hk
      (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV
      (halfEndPhysicalEvenExtension F)
    spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F t =
      A (t : ℝ) - spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0
        (A 0) t := rfl

theorem spectralHalfPotentialDirichletCLM_zero
    (F : ℝ≥0 →ᵇ SpectralSpace ι) :
    spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F 0 = 0 := by
  rw [spectralHalfPotentialDirichletCLM_apply, spectralHalfPotentialPoissonCLM_zero]
  exact sub_self _

/-- A coordinate that vanishes in the actual source also vanishes in
the constructed Dirichlet field at every nonnegative time. -/
theorem spectralHalfPotentialDirichletCLM_coordinate_zero
    (F : ℝ≥0 →ᵇ SpectralSpace ι) (i : ι) (hF : ∀ t, F t i = 0) (t : ℝ≥0) :
    spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F t i = 0 := by
  let A := halfEndFullPotentialCLM k hk₀ hk hκ0 hκ1 V hV F
  have hE (s : ℝ) : halfEndPhysicalEvenExtension F s i = 0 := by
    rw [halfEndPhysicalEvenExtension_apply]
    change Real.exp (2 * s - 2 * |s|) * F _ i = 0
    rw [hF, mul_zero]
  have hA (s : ℝ) : A s i = 0 :=
    spectralIntegralPotentialInverse_coordinate_zero k (by linarith : 0 < k₀) hk
      (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV
      (halfEndPhysicalEvenExtension F) i hE s
  rw [spectralHalfPotentialDirichletCLM_apply]
  change A (t : ℝ) i -
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 (A 0) t i = 0
  rw [hA (t : ℝ), spectralHalfPotentialPoissonCLM_coordinate_zero
    k hk₀ hk hκ0 hκ1 V hV hV0 (A 0) i (hA 0) t, sub_self]

private theorem halfEndFullPotentialCLM_norm_le
    (F : ℝ≥0 →ᵇ SpectralSpace ι) :
    ‖halfEndFullPotentialCLM k hk₀ hk hκ0 hκ1 V hV F‖ ≤
      (‖F‖ / (k₀ ^ 2 - 4)) / (1 - κ) := by
  have h := spectralIntegralPotentialInverse_norm_le k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV
    (halfEndPhysicalEvenExtension F)
  change ‖spectralIntegralPotentialInverse k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) hκ0 hκ1 V hV
    (halfEndPhysicalEvenExtension F)‖ ≤ _
  norm_num at h
  apply h.trans
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (halfEndPhysicalEvenExtension_norm_le F)
      (by nlinarith : 0 ≤ k₀ ^ 2 - 4)) (sub_pos.mpr hκ1).le

/-- A uniform operator bound requiring only the original `κ < 1`. -/
theorem spectralHalfPotentialDirichletCLM_apply_norm_le
    (F : ℝ≥0 →ᵇ SpectralSpace ι) :
    ‖spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F‖ ≤
      (2 / ((k₀ ^ 2 - 4) * (1 - κ) ^ 2)) * ‖F‖ := by
  let A := halfEndFullPotentialCLM k hk₀ hk hκ0 hκ1 V hV F
  let B := (‖F‖ / (k₀ ^ 2 - 4)) / (1 - κ)
  have hp : 0 < 1 - κ := sub_pos.mpr hκ1
  have hg : 0 < k₀ ^ 2 - 4 := by nlinarith
  have hA : ‖A‖ ≤ B := halfEndFullPotentialCLM_norm_le k hk₀ hk hκ0 hκ1 V hV F
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hB : B ≤ B / (1 - κ) := (le_div_iff₀ hp).mpr (by nlinarith)
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  rw [spectralHalfPotentialDirichletCLM_apply]
  change ‖A (t : ℝ) -
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 (A 0) t‖ ≤ _
  calc
    _ ≤ ‖A (t : ℝ)‖ +
        ‖spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 (A 0) t‖ :=
      norm_sub_le _ _
    _ ≤ B + B / (1 - κ) := add_le_add
      ((A.norm_coe_le_norm _).trans hA)
      (((BoundedContinuousFunction.norm_coe_le_norm _ _).trans
        (spectralHalfPotentialPoissonCLM_norm_le k hk₀ hk hκ0 hκ1 V hV hV0 (A 0))).trans
          (div_le_div_of_nonneg_right ((A.norm_coe_le_norm 0).trans hA) hp.le))
    _ ≤ 2 * (B / (1 - κ)) := by linarith
    _ = _ := by dsimp only [B]; field_simp <;> ring

/-- Both first differentiability and the true second derivative are
produced for the same constructed weighted coordinate. -/
theorem spectralHalfPotentialDirichletCLM_coordinate_equation
    (F : ℝ≥0 →ᵇ SpectralSpace ι) (i : ι) (t : ℝ) (ht : 0 < t) :
    let y := fun s : ℝ =>
      spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F s.toNNReal i
    DifferentiableAt ℝ y t ∧
      HasDerivAt (deriv y)
        (4 * deriv y t + (k i ^ 2 - 4 - V t) * y t + F t.toNNReal i) t := by
  let A := halfEndFullPotentialCLM k hk₀ hk hκ0 hκ1 V hV F
  let a : ℝ → ℝ := fun s => A s i
  let p : ℝ → ℝ := fun s =>
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 (A 0) s.toNNReal i
  let U : ℝ → ℝ := fun s => a s - p s
  let y : ℝ → ℝ := fun s =>
    spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F s.toNNReal i
  have hA := spectralIntegralPotentialInverse_coordinate_equation k
    (by linarith : 0 < k₀) hk (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀)
    hκ0 hκ1 V hV (halfEndPhysicalEvenExtension F) i
  change Differentiable ℝ a ∧ Differentiable ℝ (deriv a) ∧
    (∀ s, deriv (deriv a) s = -2 * (-2) * deriv a s +
      (k i ^ 2 - (-2) ^ 2) * a s + halfEndPhysicalEvenExtension F s i - V s * a s) at hA
  have hP (s : ℝ) (hs : 0 < s) : DifferentiableAt ℝ p s ∧
      HasDerivAt (deriv p) (4 * deriv p s + (k i ^ 2 - 4 - V s) * p s) s :=
    spectralHalfPotentialPoissonCLM_coordinate_equation k hk₀ hk hκ0 hκ1 V hV hV0
      (A 0) i s hs
  have hD : deriv U =ᶠ[𝓝 t] fun s => deriv a s - deriv p s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact deriv_sub (hA.1 s) (hP s hs).1
  have hU : DifferentiableAt ℝ U t := (hA.1 t).sub (hP t ht).1
  have hU2 : HasDerivAt (deriv U)
      (deriv (deriv a) t - (4 * deriv p t + (k i ^ 2 - 4 - V t) * p t)) t :=
    ((hA.2.1 t).hasDerivAt.sub (hP t ht).2).congr_of_eventuallyEq hD
  have hExt : halfEndPhysicalEvenExtension F t = F t.toNNReal := by
    have he := halfEndPhysicalEvenExtension_nonnegative F t.toNNReal
    simpa only [Real.coe_toNNReal t ht.le] using he
  have hUeq : deriv (deriv a) t - (4 * deriv p t + (k i ^ 2 - 4 - V t) * p t) =
      4 * deriv U t + (k i ^ 2 - 4 - V t) * U t + F t.toNNReal i := by
    rw [hA.2.2 t, hExt, hD.self_of_nhds]
    dsimp only [U]
    ring
  have heq : y =ᶠ[𝓝 t] U := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    dsimp only [y, U, a, p]
    rw [spectralHalfPotentialDirichletCLM_apply]
    change A (s.toNNReal : ℝ) i -
      spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 (A 0) s.toNNReal i = _
    rw [Real.coe_toNNReal s hs.le]
  change DifferentiableAt ℝ y t ∧ HasDerivAt (deriv y)
    (4 * deriv y t + (k i ^ 2 - 4 - V t) * y t + F t.toNNReal i) t
  refine ⟨(hU.hasDerivAt.congr_of_eventuallyEq heq).differentiableAt, ?_⟩
  apply (hU2.congr_of_eventuallyEq heq.deriv).congr_deriv
  rw [hUeq, heq.deriv_eq, heq.self_of_nhds]

/-- Only continuity of the original half-line source is needed for C2
regularity of each coordinate on positive time. -/
theorem spectralHalfPotentialDirichletCLM_coordinate_c2
    (F : ℝ≥0 →ᵇ SpectralSpace ι) (i : ι) :
    ContDiffOn ℝ 2 (fun s : ℝ =>
      spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F s.toNNReal i)
      (Ioi 0) := by
  let y : ℝ → ℝ := fun s =>
    spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F s.toNNReal i
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt y (deriv y t) t :=
    (spectralHalfPotentialDirichletCLM_coordinate_equation
      k hk₀ hk hκ0 hκ1 V hV hV0 F i t ht).1.hasDerivAt
  have hdd (t : ℝ) (ht : 0 < t) : HasDerivAt (deriv y)
      (4 * deriv y t + (k i ^ 2 - 4 - V t) * y t + F t.toNNReal i) t :=
    (spectralHalfPotentialDirichletCLM_coordinate_equation
      k hk₀ hk hκ0 hκ1 V hV hV0 F i t ht).2
  have hy : ContinuousOn y (Ioi 0) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdy : ContinuousOn (deriv y) (Ioi 0) :=
    fun t ht => (hdd t ht).continuousAt.continuousWithinAt
  have hcoef : ContinuousOn (fun t : ℝ => k i ^ 2 - 4 - V t) (Ioi 0) :=
    continuousOn_const.sub V.continuous.continuousOn
  have hf : Continuous (fun t : ℝ => F t.toNNReal i) :=
    (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).continuous.comp
      (F.continuous.comp continuous_real_toNNReal)
  exact contDiffOn_two_of_continuous_second_derivative isOpen_Ioi y (deriv y)
    (fun t => 4 * deriv y t + (k i ^ 2 - 4 - V t) * y t + F t.toNNReal i)
    (((continuousOn_const.mul hdy).add (hcoef.mul hy)).add hf.continuousOn) hd hdd

theorem spectralHalfPotentialDirichletCLM_physical_coordinate_c2
    (F : ℝ≥0 →ᵇ SpectralSpace ι) (i : ι) :
    ContDiffOn ℝ 2 (fun s : ℝ => Real.exp (-2 * s) *
      spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F s.toNNReal i)
      (Ioi 0) := by
  have he : ContDiff ℝ 2 (fun s : ℝ => Real.exp (-2 * s)) := by fun_prop
  exact he.contDiffOn.mul
    (spectralHalfPotentialDirichletCLM_coordinate_c2 k hk₀ hk hκ0 hκ1 V hV hV0 F i)

/-- The same physical coordinate has the correctly weighted forcing. -/
theorem spectralHalfPotentialDirichletCLM_physical_coordinate_equation
    (F : ℝ≥0 →ᵇ SpectralSpace ι) (i : ι) (t : ℝ) (ht : 0 < t) :
    let z := fun s : ℝ => Real.exp (-2 * s) *
      spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F s.toNNReal i
    HasDerivAt (deriv z)
      ((k i ^ 2 - V t) * z t + Real.exp (-2 * t) * F t.toNNReal i) t := by
  let y : ℝ → ℝ := fun s =>
    spectralHalfPotentialDirichletCLM k hk₀ hk hκ0 hκ1 V hV hV0 F s.toNNReal i
  let z : ℝ → ℝ := fun s => Real.exp (-2 * s) * y s
  have hC2 : ContDiffOn ℝ 2 z (Ioi 0) :=
    spectralHalfPotentialDirichletCLM_physical_coordinate_c2
      k hk₀ hk hκ0 hκ1 V hV hV0 F i
  have hz (s : ℝ) (hs : 0 < s) : HasDerivAt z (deriv z s) s :=
    ((hC2.contDiffAt (isOpen_Ioi.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  have hy (s : ℝ) (hs : 0 < s) : DifferentiableAt ℝ y s ∧ HasDerivAt (deriv y)
      (4 * deriv y s + ((k i ^ 2 - V s) - 4) * y s + F s.toNNReal i) s := by
    have h := spectralHalfPotentialDirichletCLM_coordinate_equation
      k hk₀ hk hκ0 hκ1 V hV hV0 F i s hs
    refine ⟨h.1, h.2.congr_deriv ?_⟩
    ring
  exact halfEnd_expTwo_forced_physical_derivative_equation
    y z (deriv z) (fun s => k i ^ 2 - V s) (fun s => F s.toNNReal i)
    (fun _ _ => rfl) hz hy t ht

#print axioms spectralHalfPotentialDirichletCLM
#print axioms spectralHalfPotentialDirichletCLM_zero
#print axioms spectralHalfPotentialDirichletCLM_coordinate_zero
#print axioms spectralHalfPotentialDirichletCLM_apply_norm_le
#print axioms spectralHalfPotentialDirichletCLM_coordinate_equation
#print axioms spectralHalfPotentialDirichletCLM_coordinate_c2
#print axioms spectralHalfPotentialDirichletCLM_physical_coordinate_c2
#print axioms spectralHalfPotentialDirichletCLM_physical_coordinate_equation

end Yamabe3.Analysis.Delaunay
