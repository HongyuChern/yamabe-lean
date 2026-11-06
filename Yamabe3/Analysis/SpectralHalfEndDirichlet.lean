import Yamabe3.Analysis.SpectralCoordinateEquation
import Yamabe3.Analysis.SpectralFirstDerivativeKernel
import PoincareLib.Analysis.Parabolic.Dirichlet.SpectralSemigroup

/-!
# A constructed half-line Dirichlet inverse in the common weight minus two

A bounded continuous half-line source is extended evenly as an actual
physical source. Its weighted extension is exp(2t-2|t|) F(|t|), which is
continuous at the entrance and has norm at most the original norm. The
already constructed whole-line free inverse is then corrected by its
actual decaying Poisson solution with the same entrance value.

The correction has literal zero entrance value. All operators are genuine
continuous linear maps on the complete bounded-continuous Hilbert-valued
spaces. This file does not prescribe a free inverse or boundary solver as
an input, and does not assume a bounded H1 lifting of arbitrary L2 data.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory
open scoped NNReal Topology lp BoundedContinuousFunction RealInnerProductSpace

namespace Yamabe3.Analysis.Delaunay

private def halfEndAbsTime (t : ℝ) : ℝ≥0 := ⟨|t|, abs_nonneg t⟩

private theorem halfEndAbsTime_continuous : Continuous halfEndAbsTime :=
  continuous_abs.subtype_mk _

section Extension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem halfEndEven_factor_le (t : ℝ) : Real.exp (2 * t - 2 * |t|) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  linarith only [le_abs_self t]

/-- Even extension of the physical source, expressed in its common
weight minus two. The value at zero is continuous, not an odd jump. -/
def halfEndPhysicalEvenExtension (F : ℝ≥0 →ᵇ E) : ℝ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => Real.exp (2 * t - 2 * |t|) • F (halfEndAbsTime t))
    (by apply Continuous.smul
        · fun_prop
        · exact F.continuous.comp halfEndAbsTime_continuous)
    ‖F‖ (fun t => by
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_of_le_one_left (norm_nonneg _) (halfEndEven_factor_le t)).trans
        (F.norm_coe_le_norm _))

theorem halfEndPhysicalEvenExtension_apply (F : ℝ≥0 →ᵇ E) (t : ℝ) :
    halfEndPhysicalEvenExtension F t =
      Real.exp (2 * t - 2 * |t|) • F (halfEndAbsTime t) := rfl

theorem halfEndPhysicalEvenExtension_nonnegative (F : ℝ≥0 →ᵇ E) (t : ℝ≥0) :
    halfEndPhysicalEvenExtension F (t : ℝ) = F t := by
  rw [halfEndPhysicalEvenExtension_apply, abs_of_nonneg t.coe_nonneg, sub_self,
    Real.exp_zero, one_smul]
  congr 1
  apply Subtype.ext
  exact abs_of_nonneg t.coe_nonneg

theorem halfEndPhysicalEvenExtension_norm_le (F : ℝ≥0 →ᵇ E) :
    ‖halfEndPhysicalEvenExtension F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro t
  rw [halfEndPhysicalEvenExtension_apply, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_of_le_one_left (norm_nonneg _) (halfEndEven_factor_le t)).trans
    (F.norm_coe_le_norm _)

def halfEndPhysicalEvenExtensionCLM : (ℝ≥0 →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  ({ toFun := halfEndPhysicalEvenExtension
     map_add' := by
       intro F G
       apply BoundedContinuousFunction.ext
       intro t
       change Real.exp (2 * t - 2 * |t|) • (F (halfEndAbsTime t) + G (halfEndAbsTime t)) = _
       exact smul_add _ _ _
     map_smul' := by
       intro c F
       apply BoundedContinuousFunction.ext
       intro t
       change Real.exp (2 * t - 2 * |t|) • (c • F (halfEndAbsTime t)) =
         c • (Real.exp (2 * t - 2 * |t|) • F (halfEndAbsTime t))
       exact smul_comm _ _ _ } : (ℝ≥0 →ᵇ E) →ₗ[ℝ] (ℝ →ᵇ E)).mkContinuous 1
    (fun F => by
      change ‖halfEndPhysicalEvenExtension F‖ ≤ 1 * ‖F‖
      simpa only [one_mul] using halfEndPhysicalEvenExtension_norm_le F)

def halfEndRestriction (F : ℝ →ᵇ E) : ℝ≥0 →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => F (t : ℝ))
    (F.continuous.comp continuous_subtype_val) ‖F‖ (fun t => F.norm_coe_le_norm _)

def halfEndRestrictionCLM : (ℝ →ᵇ E) →L[ℝ] (ℝ≥0 →ᵇ E) :=
  ({ toFun := halfEndRestriction
     map_add' := by intro F G; rfl
     map_smul' := by intro c F; rfl } : (ℝ →ᵇ E) →ₗ[ℝ] (ℝ≥0 →ᵇ E)).mkContinuous 1
    (fun F => by
      simp only [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
      intro t
      exact F.norm_coe_le_norm _)

end Extension

section Poisson

variable {ι : Type*} (k : ι → ℝ) {k₀ : ℝ} (hk₀ : 2 < k₀) (hk : ∀ i, k₀ ≤ k i)

private def spectralHalfRate (i : ι) : ℝ≥0 :=
  ⟨k i, by have := hk i; linarith⟩

private theorem spectralPoissonKernel_strongContinuous_nonnegative (u : SpectralSpace ι) :
    Continuous (fun t : ℝ≥0 =>
      spectralPoissonKernel k (by linarith : 0 < k₀) hk (t : ℝ) u) := by
  let b : HilbertBasis ι ℝ (SpectralSpace ι) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)
  have he (t : ℝ≥0) :
      Poincare.Analysis.Dirichlet.Spectral.heat b (spectralHalfRate k hk₀ hk) t u =
        spectralPoissonKernel k (by linarith : 0 < k₀) hk (t : ℝ) u := by
    ext i
    have h := Poincare.Analysis.Dirichlet.Spectral.heat_repr b
      (spectralHalfRate k hk₀ hk) t u i
    change Poincare.Analysis.Dirichlet.Spectral.heat b
      (spectralHalfRate k hk₀ hk) t u i =
      Real.exp (-k i * (t : ℝ)) * u i at h
    rw [spectralPoissonKernel_apply, abs_of_nonneg t.coe_nonneg]
    exact h
  exact (Poincare.Analysis.Dirichlet.Spectral.continuous_heat b
    (spectralHalfRate k hk₀ hk) u).congr he

private theorem spectralHalfPoisson_apply_bound (u : SpectralSpace ι) (t : ℝ≥0) :
    ‖Real.exp (2 * (t : ℝ)) •
      spectralPoissonKernel k (by linarith : 0 < k₀) hk (t : ℝ) u‖ ≤ ‖u‖ := by
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (2 * (t : ℝ)) * Real.exp (-k₀ * (t : ℝ)) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    nlinarith only [hk₀, t.coe_nonneg]
  calc
    _ ≤ Real.exp (2 * (t : ℝ)) *
        (‖spectralPoissonKernel k (by linarith : 0 < k₀) hk (t : ℝ)‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.exp_pos _).le
    _ ≤ Real.exp (2 * (t : ℝ)) * (Real.exp (-k₀ * |(t : ℝ)|) * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (spectralPoissonKernel_norm_le k (by linarith : 0 < k₀) hk (t : ℝ))
          (norm_nonneg u)) (Real.exp_pos _).le
    _ ≤ ‖u‖ := by
      rw [abs_of_nonneg t.coe_nonneg, ← mul_assoc]
      exact mul_le_of_le_one_left (norm_nonneg u) hexp

/-- The actual free Poisson curve expressed in the exp(2t) topology. -/
def spectralHalfPoisson (u : SpectralSpace ι) : ℝ≥0 →ᵇ SpectralSpace ι :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => Real.exp (2 * (t : ℝ)) •
      spectralPoissonKernel k (by linarith : 0 < k₀) hk (t : ℝ) u)
    ((by fun_prop : Continuous (fun t : ℝ≥0 => Real.exp (2 * (t : ℝ)))).smul
      (spectralPoissonKernel_strongContinuous_nonnegative k hk₀ hk u))
    ‖u‖ (spectralHalfPoisson_apply_bound k hk₀ hk u)

theorem spectralHalfPoisson_coordinate (u : SpectralSpace ι) (t : ℝ≥0) (i : ι) :
    spectralHalfPoisson k hk₀ hk u t i = Real.exp ((2 - k i) * (t : ℝ)) * u i := by
  change Real.exp (2 * (t : ℝ)) *
    (Real.exp (-k i * |(t : ℝ)|) * u i) = _
  rw [abs_of_nonneg t.coe_nonneg, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem spectralHalfPoisson_norm_le (u : SpectralSpace ι) :
    ‖spectralHalfPoisson k hk₀ hk u‖ ≤ ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg u)).mpr
  exact spectralHalfPoisson_apply_bound k hk₀ hk u

def spectralHalfPoissonCLM : SpectralSpace ι →L[ℝ] (ℝ≥0 →ᵇ SpectralSpace ι) :=
  ({ toFun := spectralHalfPoisson k hk₀ hk
     map_add' := by
       intro u v
       apply BoundedContinuousFunction.ext
       intro t
       ext i
       simp only [spectralHalfPoisson_coordinate, lp.coeFn_add, Pi.add_apply,
         BoundedContinuousFunction.add_apply]
       ring
     map_smul' := by
       intro c u
       apply BoundedContinuousFunction.ext
       intro t
       ext i
       simp only [spectralHalfPoisson_coordinate, lp.coeFn_smul, Pi.smul_apply,
         BoundedContinuousFunction.smul_apply, smul_eq_mul, RingHom.id_apply]
       ring } : SpectralSpace ι →ₗ[ℝ] (ℝ≥0 →ᵇ SpectralSpace ι)).mkContinuous 1
    (fun u => by
      change ‖spectralHalfPoisson k hk₀ hk u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using spectralHalfPoisson_norm_le k hk₀ hk u)

theorem spectralHalfPoisson_zero (u : SpectralSpace ι) :
    spectralHalfPoisson k hk₀ hk u 0 = u := by
  ext i
  simp only [spectralHalfPoisson_coordinate, NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul]

end Poisson

section Dirichlet

variable {ι : Type*} (k : ι → ℝ) {k₀ : ℝ} (hk₀ : 2 < k₀) (hk : ∀ i, k₀ ≤ k i)

include hk₀ in
private theorem halfEnd_gap_positive : 0 < k₀ ^ 2 - 4 := by nlinarith

private def halfEndFullFreeCLM :
    (ℝ≥0 →ᵇ SpectralSpace ι) →L[ℝ] (ℝ →ᵇ SpectralSpace ι) :=
  (spectralResolventCLM k (by linarith : 0 < k₀) hk
    (by simpa only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hk₀ :
      |(-2 : ℝ)| < k₀)).comp halfEndPhysicalEvenExtensionCLM

/-- A constructed zero Dirichlet inverse. The second term removes the
actual entrance value of the first term by a homogeneous decaying curve. -/
def spectralHalfDirichletCLM :
    (ℝ≥0 →ᵇ SpectralSpace ι) →L[ℝ] (ℝ≥0 →ᵇ SpectralSpace ι) :=
  halfEndRestrictionCLM.comp (halfEndFullFreeCLM k hk₀ hk) -
    (spectralHalfPoissonCLM k hk₀ hk).comp
      ((BoundedContinuousFunction.evalCLM (𝕜 := ℝ) 0).comp (halfEndFullFreeCLM k hk₀ hk))

theorem spectralHalfDirichletCLM_apply (F : ℝ≥0 →ᵇ SpectralSpace ι) (t : ℝ≥0) :
    spectralHalfDirichletCLM k hk₀ hk F t =
      halfEndFullFreeCLM k hk₀ hk F (t : ℝ) -
        spectralHalfPoisson k hk₀ hk (halfEndFullFreeCLM k hk₀ hk F 0) t := rfl

theorem spectralHalfDirichletCLM_zero (F : ℝ≥0 →ᵇ SpectralSpace ι) :
    spectralHalfDirichletCLM k hk₀ hk F 0 = 0 := by
  rw [spectralHalfDirichletCLM_apply, spectralHalfPoisson_zero]
  exact sub_self _

private theorem halfEndFullFreeCLM_norm_le (F : ℝ≥0 →ᵇ SpectralSpace ι) :
    ‖halfEndFullFreeCLM k hk₀ hk F‖ ≤ ‖F‖ / (k₀ ^ 2 - 4) := by
  have h := spectralResolvent_norm_le k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) (halfEndPhysicalEvenExtension F)
  change ‖spectralResolvent k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) (halfEndPhysicalEvenExtension F)‖ ≤ _
  norm_num at h
  exact h.trans (div_le_div_of_nonneg_right (halfEndPhysicalEvenExtension_norm_le F)
    (halfEnd_gap_positive hk₀).le)

/-- A coarse uniform bound, sufficient to construct the actual operator.
Sharper potential row bounds are proved separately from its reflected kernel. -/
theorem spectralHalfDirichletCLM_apply_norm_le (F : ℝ≥0 →ᵇ SpectralSpace ι) :
    ‖spectralHalfDirichletCLM k hk₀ hk F‖ ≤ (2 / (k₀ ^ 2 - 4)) * ‖F‖ := by
  let W := halfEndFullFreeCLM k hk₀ hk F
  have hW : ‖W‖ ≤ ‖F‖ / (k₀ ^ 2 - 4) := halfEndFullFreeCLM_norm_le k hk₀ hk F
  have hgap : 0 < k₀ ^ 2 - 4 := halfEnd_gap_positive hk₀
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  rw [spectralHalfDirichletCLM_apply]
  calc
    _ ≤ ‖W (t : ℝ)‖ + ‖spectralHalfPoisson k hk₀ hk (W 0) t‖ := norm_sub_le _ _
    _ ≤ ‖W‖ + ‖W 0‖ := add_le_add (W.norm_coe_le_norm _)
      ((BoundedContinuousFunction.norm_coe_le_norm _ t).trans
        (spectralHalfPoisson_norm_le k hk₀ hk (W 0)))
    _ ≤ ‖W‖ + ‖W‖ := add_le_add le_rfl (W.norm_coe_le_norm 0)
    _ ≤ 2 * (‖F‖ / (k₀ ^ 2 - 4)) := by linarith only [hW]
    _ = _ := by ring

/-- The same constructed half-line curve satisfies the genuine weighted
free equation on every positive time.  Only continuity of its source is
needed to differentiate each actual spectral coordinate twice. -/
theorem spectralHalfDirichletCLM_coordinate_equation
    (F : ℝ≥0 →ᵇ SpectralSpace ι) (i : ι) (t : ℝ) (ht : 0 < t) :
    let y := fun s : ℝ => spectralHalfDirichletCLM k hk₀ hk F s.toNNReal i
    HasDerivAt (deriv y)
      (4 * deriv y t + (k i ^ 2 - 4) * y t + F t.toNNReal i) t := by
  dsimp only
  let A := halfEndFullFreeCLM k hk₀ hk F
  let q : ℝ → ℝ := fun s => Real.exp ((2 - k i) * s) * A 0 i
  let U : ℝ → ℝ := fun s => A s i - q s
  let y : ℝ → ℝ := fun s => spectralHalfDirichletCLM k hk₀ hk F s.toNNReal i
  have hA := spectralResolvent_coordinate_equation k (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀) (halfEndPhysicalEvenExtension F) i
  change Differentiable ℝ (fun s => A s i) ∧
    Differentiable ℝ (deriv (fun s => A s i)) ∧
    (∀ s, deriv (deriv (fun x => A x i)) s =
      -2 * (-2) * deriv (fun x => A x i) s +
        (k i ^ 2 - (-2) ^ 2) * A s i + halfEndPhysicalEvenExtension F s i) at hA
  have hq (s : ℝ) : HasDerivAt q ((2 - k i) * q s) s := by
    apply (((hasDerivAt_id s).const_mul (2 - k i)).exp.mul_const (A 0 i)).congr_deriv
    dsimp only [q, id_eq]
    ring
  have hqD : deriv q = fun s => (2 - k i) * q s := funext (fun s => (hq s).deriv)
  have hqDiff : Differentiable ℝ q := fun s => (hq s).differentiableAt
  have hqDDiff : Differentiable ℝ (deriv q) := by
    rw [hqD]
    exact fun s => ((hq s).const_mul (2 - k i)).differentiableAt
  have hqDD (s : ℝ) : deriv (deriv q) s = (2 - k i) ^ 2 * q s := by
    rw [hqD, ((hq s).const_mul (2 - k i)).deriv]
    ring
  have hU : Differentiable ℝ U := hA.1.sub hqDiff
  have hUD : deriv U = fun s => deriv (fun x => A x i) s - deriv q s := by
    funext s
    exact deriv_sub (hA.1 s) (hqDiff s)
  have hUDDiff : Differentiable ℝ (deriv U) := by
    rw [hUD]
    exact hA.2.1.sub hqDDiff
  have hUEquation : deriv (deriv U) t =
      4 * deriv U t + (k i ^ 2 - 4) * U t + F t.toNNReal i := by
    have hExt : halfEndPhysicalEvenExtension F t = F t.toNNReal := by
      have he := halfEndPhysicalEvenExtension_nonnegative F t.toNNReal
      simpa only [Real.coe_toNNReal t ht.le] using he
    have hsub := ((hA.2.1 t).hasDerivAt.sub (hqDDiff t).hasDerivAt)
    change HasDerivAt
      (fun s => deriv (fun x => A x i) s - deriv q s)
      (deriv (deriv (fun x => A x i)) t - deriv (deriv q) t) t at hsub
    rw [hUD, hsub.deriv, hA.2.2 t, hqDD t, hqD, hExt]
    dsimp only [U]
    ring
  have heq : y =ᶠ[𝓝 t] U := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    dsimp only [y, U, q]
    rw [spectralHalfDirichletCLM_apply]
    change A (s.toNNReal : ℝ) i -
      spectralHalfPoisson k hk₀ hk (A 0) s.toNNReal i = _
    rw [spectralHalfPoisson_coordinate, Real.coe_toNNReal s hs.le]
  change HasDerivAt (deriv y) (4 * deriv y t + (k i ^ 2 - 4) * y t + F t.toNNReal i) t
  apply ((hUDDiff t).hasDerivAt.congr_of_eventuallyEq heq.deriv).congr_deriv
  rw [hUEquation, heq.deriv_eq, heq.self_of_nhds]

#print axioms halfEndPhysicalEvenExtensionCLM
#print axioms spectralHalfPoissonCLM
#print axioms spectralHalfDirichletCLM
#print axioms spectralHalfDirichletCLM_zero
#print axioms spectralHalfDirichletCLM_apply_norm_le
#print axioms spectralHalfDirichletCLM_coordinate_equation

end Dirichlet

end Yamabe3.Analysis.Delaunay
