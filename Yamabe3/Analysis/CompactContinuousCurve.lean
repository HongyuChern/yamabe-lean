import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Differentiation of actual compact-parameter continuous-function curves

The Banach-valued derivative is proved from the actual pointwise
fundamental theorem of calculus and the genuine evaluation continuous
linear maps. A continuous tower of pointwise derivatives consequently
gives full smoothness in the sup norm, and therefore in native Lp.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A jointly continuous derivative is a derivative in the genuine sup norm.
The proof integrates it in C(X,R), then checks the equality by evaluation. -/
theorem hasDerivAt_continuousMap_curve {P Q : ℝ → C(X, ℝ)}
    (hQ : Continuous Q) (hderiv : ∀ t x, HasDerivAt (fun s => P s x) (Q t x) t)
    (t : ℝ) : HasDerivAt P (Q t) t := by
  have hFTC (s : ℝ) : (∫ r in t..s, Q r) = P s - P t := by
    apply ContinuousMap.ext
    intro x
    have hEval : (∫ r in t..s, (ContinuousMap.evalCLM ℝ x) (Q r)) =
        (ContinuousMap.evalCLM ℝ x) (∫ r in t..s, Q r) :=
      (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm (hQ.intervalIntegrable _ _)
    change (ContinuousMap.evalCLM ℝ x) (∫ r in t..s, Q r) = P s x - P t x
    rw [← hEval]
    change (∫ r in t..s, Q r x) = P s x - P t x
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r x)
    exact ((ContinuousMap.evalCLM ℝ x).continuous.comp hQ).intervalIntegrable _ _
  have heq : (fun s => P t + ∫ r in t..s, Q r) = P := by
    funext s
    rw [hFTC]
    abel
  have hd : HasDerivAt (fun s => ∫ r in t..s, Q r) (Q t) t :=
    intervalIntegral.integral_hasDerivAt_right (hQ.intervalIntegrable _ _)
      hQ.aestronglyMeasurable.stronglyMeasurableAtFilter hQ.continuousAt
  simpa only [heq] using hd.const_add (P t)

/-- The derivative tower is pointwise input; its sup-norm differentiability
is a theorem. No Banach-valued smoothness is assumed. -/
theorem contDiff_continuousMap_curve_of_tower (P : ℕ → ℝ → C(X, ℝ))
    (hP : ∀ n, Continuous (P n))
    (hD : ∀ n t x, HasDerivAt (fun s => P n s x) (P (n + 1) t x) t) :
    ∀ n, ContDiff ℝ ∞ (P n) := by
  have hd (n : ℕ) : Differentiable ℝ (P n) := fun t =>
    (hasDerivAt_continuousMap_curve (hP (n + 1)) (hD n) t).differentiableAt
  have hderiv (n : ℕ) : deriv (P n) = P (n + 1) :=
    funext fun t => (hasDerivAt_continuousMap_curve (hP (n + 1)) (hD n) t).deriv
  have hall : ∀ k : ℕ, ∀ n, ContDiff ℝ k (P n) := by
    intro k
    induction k with
    | zero => exact fun n => contDiff_zero.mpr (hP n)
    | succ k ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨hd n, by simp, ?_⟩
      rw [hderiv]
      exact ih (n + 1)
  exact fun n => contDiff_infty.mpr (fun k => hall k n)

/-- Joint continuity of the pointwise tower suffices to form the actual
smooth C(X,R)-valued curve. -/
theorem contDiff_curry_of_pointwise_tower (f : ℕ → ℝ × X → ℝ)
    (hf : ∀ n, Continuous (f n))
    (hD : ∀ n t x, HasDerivAt (fun s => f n (s, x)) (f (n + 1) (t, x)) t) :
    ContDiff ℝ ∞ (fun t => (ContinuousMap.curry ⟨f 0, hf 0⟩) t) := by
  exact contDiff_continuousMap_curve_of_tower
    (fun n t => (ContinuousMap.curry ⟨f n, hf n⟩) t)
    (fun n => (ContinuousMap.curry ⟨f n, hf n⟩).continuous) hD 0

/-- The actual finite-measure L2 inclusion preserves the constructed
smooth curve, with no pointwise-representative choice in its definition. -/
theorem contDiff_L2_of_pointwise_tower [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : ℕ → ℝ × X → ℝ)
    (hf : ∀ n, Continuous (f n))
    (hD : ∀ n t x, HasDerivAt (fun s => f n (s, x)) (f (n + 1) (t, x)) t) :
    ContDiff ℝ ∞ (fun t => ContinuousMap.toLp 2 ν ℝ
      ((ContinuousMap.curry ⟨f 0, hf 0⟩) t)) :=
  (ContinuousMap.toLp (E := ℝ) 2 ν ℝ : C(X, ℝ) →L[ℝ] Lp ℝ 2 ν).contDiff.comp
    (contDiff_curry_of_pointwise_tower f hf hD)

end Yamabe3.Analysis.Delaunay
