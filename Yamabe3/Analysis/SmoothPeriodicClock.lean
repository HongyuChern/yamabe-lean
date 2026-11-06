import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The actual smooth inverse of a positive periodic time integral

The inverse is constructed from a genuine integral, strict monotonicity and
the intermediate value theorem. Its smoothness and derivative are proved by
the inverse theorem. The period shift is inherited from the actual integral
of the positive periodic time density. This is used to construct Delaunay
orbits from an explicit energy oval, without a phase-portrait existence field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace Yamabe3.Analysis.Delaunay

/-- The actual elapsed time from the chosen angular base point. -/
def timePrimitive (f : ℝ → ℝ) (b x : ℝ) : ℝ := ∫ t in b..x, f t

theorem timePrimitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (b x : ℝ) :
    HasDerivAt (timePrimitive f b) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem timePrimitive_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (b : ℝ) :
    ContDiff ℝ ∞ (timePrimitive f b) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (timePrimitive_hasDerivAt hf.continuous b x).differentiableAt, ?_⟩
  have hderiv : deriv (timePrimitive f b) = f :=
    funext fun x => (timePrimitive_hasDerivAt hf.continuous b x).deriv
  rw [hderiv]
  exact hf

private theorem integral_lower_bound {f : ℝ → ℝ} (hf : Continuous f)
    {c : ℝ} (hlower : ∀ x, c ≤ f x) {x y : ℝ} (hxy : x ≤ y) :
    c * (y - x) ≤ ∫ t in x..y, f t := by
  have h := intervalIntegral.integral_mono_on (μ := volume) hxy
    ((show Continuous (fun _ : ℝ => c) from continuous_const).intervalIntegrable x y) (hf.intervalIntegrable x y)
    (fun t _ => hlower t)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

/-- A strictly positive uniform lower bound on the time density makes the
actual primitive onto the whole real line. The proof exhibits finite
bracketing intervals for each target time and applies the actual IVT. -/
theorem timePrimitive_surjective {f : ℝ → ℝ} (hf : Continuous f)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c ≤ f x) (b : ℝ) :
    Function.Surjective (timePrimitive f b) := by
  intro y
  let d : ℝ := (|y| + 1) / c
  have hd : 0 < d := div_pos (by positivity) hc
  have hcd : c * d = |y| + 1 := by dsimp [d]; field_simp
  have hL := integral_lower_bound hf hlower (show b - d ≤ b by linarith)
  have hR := integral_lower_bound hf hlower (show b ≤ b + d by linarith)
  have hleft : timePrimitive f b (b - d) ≤ y := by
    unfold timePrimitive
    rw [intervalIntegral.integral_symm]
    have hh : c * d ≤ ∫ t in b - d..b, f t := by simpa only [sub_sub_cancel] using hL
    linarith [neg_abs_le y]
  have hright : y ≤ timePrimitive f b (b + d) := by
    have hh : c * d ≤ ∫ t in b..b + d, f t := by simpa only [add_sub_cancel_left] using hR
    change y ≤ ∫ t in b..b + d, f t
    linarith [le_abs_self y]
  have hcont : Continuous (timePrimitive f b) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (timePrimitive_hasDerivAt hf b x).differentiableAt.continuousAt)
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (show b - d ≤ b + d by linarith)
    hcont.continuousOn ⟨hleft, hright⟩
  exact ⟨x, hx⟩

/-- An actual positive smooth periodic density defines a global smooth time
inverse with the proved derivative and exact angular shift. All existence,
continuity, invertibility and smoothness are constructed inside the proof. -/
theorem exists_smooth_periodic_clock_inverse
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {P : ℝ} (hP : 0 < P)
    (hperiod : Function.Periodic f P) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x, c ≤ f x) (b : ℝ) :
    ∃ (θ : ℝ → ℝ) (T : ℝ),
      T = (∫ x in b..b + P, f x) ∧ 0 < T ∧
      ContDiff ℝ ∞ θ ∧ StrictMono θ ∧ θ 0 = b ∧
      (∀ t, HasDerivAt θ (f (θ t))⁻¹ t) ∧
      (∀ t, timePrimitive f b (θ t) = t) ∧
      (∀ x, θ (timePrimitive f b x) = x) ∧
      ∀ t, θ (t + T) = θ t + P := by
  have hfpos : ∀ x, 0 < f x := fun x => hc.trans_le (hlower x)
  have hmono : StrictMono (timePrimitive f b) :=
    strictMono_of_hasDerivAt_pos (timePrimitive_hasDerivAt hf.continuous b) hfpos
  have hsurj := timePrimitive_surjective hf.continuous hc hlower b
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse (timePrimitive f b) hmono
    (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
  let θ : ℝ → ℝ := e.symm
  let T : ℝ := ∫ x in b..b + P, f x
  have hright (t : ℝ) : timePrimitive f b (θ t) = t := e.apply_symm_apply t
  have hleft (x : ℝ) : θ (timePrimitive f b x) = x := e.symm_apply_apply x
  have hθzero : θ 0 = b := by simpa only [timePrimitive, intervalIntegral.integral_same] using hleft b
  have hθs : ContDiff ℝ ∞ θ :=
    e.toHomeomorph.contDiff_symm_deriv (fun x => (hfpos x).ne')
      (timePrimitive_hasDerivAt hf.continuous b) (timePrimitive_contDiff hf b)
  have hθd (t : ℝ) : HasDerivAt θ (f (θ t))⁻¹ t :=
    HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
      (timePrimitive_hasDerivAt hf.continuous b (θ t)) (hfpos (θ t)).ne'
      (Eventually.of_forall hright)
  have hT : 0 < T := by
    have h := integral_lower_bound hf.continuous hlower (show b ≤ b + P by linarith)
    have hh : c * P ≤ T := by simpa only [add_sub_cancel_left] using h
    exact (mul_pos hc hP).trans_le hh
  have hshift (x : ℝ) : timePrimitive f b (x + P) = timePrimitive f b x + T :=
    hperiod.intervalIntegral_add_eq_add b x (fun s t => hf.continuous.intervalIntegrable s t)
  refine ⟨θ, T, rfl, hT, hθs, e.symm.strictMono, hθzero, hθd, hright, hleft, ?_⟩
  intro t
  apply hmono.injective
  rw [hright, hshift, hright]

#print axioms timePrimitive_surjective
#print axioms exists_smooth_periodic_clock_inverse

end Yamabe3.Analysis.Delaunay
