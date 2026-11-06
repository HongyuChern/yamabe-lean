import Yamabe3.Analysis.SpectralPotentialInverse
import Yamabe3.Analysis.TwoRateKernelInverse

/-!
# Actual equations for every coordinate of the Hilbert inverse

Continuous coordinate evaluation commutes with the genuine Bochner
integral. A measure-preserving time reflection then identifies that
integral with the already differentiated two-rate scalar inverse.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralCoordinate_bound {ι : Type*} (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) (i : ι) :
    |F t i| ≤ ‖F‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (F t) i
  have h' : |F t i| ≤ ‖F t‖ := by simpa only [Real.norm_eq_abs] using h
  exact h'.trans (F.norm_coe_le_norm t)

theorem spectralCoordinate_continuous {ι : Type*} (F : ℝ →ᵇ SpectralSpace ι) (i : ι) :
    Continuous (fun t => F t i) :=
  (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).continuous.comp F.continuous

/-- Genuine bounded continuous coordinate of the Hilbert-valued source. -/
def spectralCoordinateFunction {ι : Type*} (F : ℝ →ᵇ SpectralSpace ι) (i : ι) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => F t i)
    (spectralCoordinate_continuous F i) ‖F‖
    (fun t => by simpa only [Real.norm_eq_abs] using spectralCoordinate_bound F t i)

/-- The actual Bochner integral, evaluated in a coordinate, is the true
two-rate inverse, with no interchange of an infinite sum and a supremum. -/
theorem spectralConvolution_coordinate {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (t : ℝ) (i : ι) :
    spectralConvolution k hk₀ hk δ F t i =
      twoRateInverse (k i + δ) (k i - δ) (fun y => F y i) t := by
  let ev := lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i
  have hi := spectralConvolution_integrable k hk₀ hk hδ F t
  have hev (s : ℝ) : ev (weightedSpectralKernel k hk₀ hk δ s (F (t - s))) =
      Real.exp (-δ * s) * scalarGreenKernel (k i) s * F (t - s) i := by
    change Real.exp (-δ * s) * (scalarGreenKernel (k i) s * F (t - s) i) = _
    ring
  have hc : spectralConvolution k hk₀ hk δ F t i =
      ∫ s : ℝ, Real.exp (-δ * s) * scalarGreenKernel (k i) s * F (t - s) i := by
    change ev (∫ s : ℝ, weightedSpectralKernel k hk₀ hk δ s (F (t - s))) = _
    rw [← ev.integral_comp_comm hi]
    exact integral_congr_ae (Eventually.of_forall hev)
  have hci : Integrable (fun s : ℝ => Real.exp (-δ * s) * scalarGreenKernel (k i) s * F (t - s) i) := by
    exact (ev.integrable_comp hi).congr (Eventually.of_forall hev)
  let Q : ℝ → ℝ := fun y =>
    Real.exp (-δ * (t - y)) * scalarGreenKernel (k i) (t - y) * F y i
  have hQ : Integrable Q := by
    convert hci.comp_sub_left t using 1
    funext y
    simp only [Q, sub_sub_cancel]
  have hchange : spectralConvolution k hk₀ hk δ F t i = ∫ y : ℝ, Q y := by
    rw [hc, ← integral_sub_left_eq_self
      (fun s : ℝ => Real.exp (-δ * s) * scalarGreenKernel (k i) s * F (t - s) i) volume t]
    simp only [sub_sub_cancel]
    rfl
  have hL (y : ℝ) (hy : y ∈ Iic t) :
      Q y = (Real.exp (-(k i + δ) * t) / (-(2 * k i))) *
        (Real.exp ((k i + δ) * y) * F y i) := by
    dsimp [Q, scalarGreenKernel]
    rw [abs_of_nonneg (sub_nonneg.mpr hy)]
    have he : Real.exp (-δ * (t - y)) * Real.exp (-k i * (t - y)) =
        Real.exp (-(k i + δ) * t) * Real.exp ((k i + δ) * y) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = -(Real.exp (-δ * (t - y)) * Real.exp (-k i * (t - y)) * F y i) / (2 * k i) := by ring
      _ = _ := by rw [he]; ring
  have hR (y : ℝ) (hy : y ∈ Ioi t) :
      Q y = (Real.exp ((k i - δ) * t) / (-(2 * k i))) *
        (Real.exp (-(k i - δ) * y) * F y i) := by
    dsimp [Q, scalarGreenKernel]
    rw [abs_of_nonpos (sub_nonpos.mpr hy.le)]
    have he : Real.exp (-δ * (t - y)) * Real.exp (-k i * -(t - y)) =
        Real.exp ((k i - δ) * t) * Real.exp (-(k i - δ) * y) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = -(Real.exp (-δ * (t - y)) * Real.exp (-k i * -(t - y)) * F y i) / (2 * k i) := by ring
      _ = _ := by rw [he]; ring
  rw [hchange, ← integral_add_compl measurableSet_Iic hQ, compl_Iic]
  rw [setIntegral_congr_fun measurableSet_Iic hL, setIntegral_congr_fun measurableSet_Ioi hR,
    integral_const_mul, integral_const_mul]
  unfold twoRateInverse leftTail rightTail
  have hsum : k i + δ + (k i - δ) = 2 * k i := by ring
  rw [hsum]
  ring

theorem spectralResolvent_coordinate_equation {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (F : ℝ →ᵇ SpectralSpace ι) (i : ι) :
    let u := fun t => spectralResolvent k hk₀ hk hδ F t i
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      ∀ t, deriv (deriv u) t = -2 * δ * deriv u t +
        ((k i) ^ 2 - δ ^ 2) * u t + F t i := by
  dsimp only
  have hr : 0 < k i + δ := by linarith [(abs_lt.mp hδ).1, hk i]
  have hs : 0 < k i - δ := by linarith [(abs_lt.mp hδ).2, hk i]
  have heq : (fun t => spectralResolvent k hk₀ hk hδ F t i) =
      twoRateInverse (k i + δ) (k i - δ) (fun y => F y i) := by
    funext t
    exact spectralConvolution_coordinate k hk₀ hk hδ F t i
  rw [heq]
  obtain ⟨hd, hdd, ho⟩ := twoRateInverse_differentiable_equation hr hs
    (spectralCoordinate_continuous F i) (fun t => spectralCoordinate_bound F t i)
  refine ⟨hd, hdd, fun t => ?_⟩
  rw [ho, congrFun heq t]
  ring

theorem spectralPotentialInverse_coordinate_equation {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k₀ ^ 2 - δ ^ 2)
    (F : ℝ →ᵇ SpectralSpace ι) (i : ι) :
    let u := fun t => spectralPotentialInverse k hk₀ hk hδ V hV F t i
    Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      ∀ t, deriv (deriv u) t = -2 * δ * deriv u t +
        ((k i) ^ 2 - δ ^ 2) * u t + F t i - V t * u t := by
  dsimp only
  let U := spectralPotentialInverse k hk₀ hk hδ V hV F
  have heq : (fun t => spectralResolvent k hk₀ hk hδ (F - V • U) t i) =
      fun t => U t i := by
    funext t
    exact congrArg (fun H : ℝ →ᵇ SpectralSpace ι => H t i)
      (spectralPotentialInverse_fixed k hk₀ hk hδ V hV F)
  have h := spectralResolvent_coordinate_equation k hk₀ hk hδ (F - V • U) i
  dsimp only at h
  rw [heq] at h
  refine ⟨h.1, h.2.1, fun t => ?_⟩
  have he := h.2.2 t
  rw [congrFun heq t] at he
  change deriv (deriv (fun t => U t i)) t = -2 * δ * deriv (fun t => U t i) t +
    ((k i) ^ 2 - δ ^ 2) * U t i + (F t i - V t * U t i) at he
  simpa only [add_sub_assoc] using he

/-- A zero source coordinate stays zero in the actual common-potential
fixed point. This will remove the real native low angular modes. -/
theorem spectralPotentialInverse_coordinate_zero {ι : Type*} (k : ι → ℝ) {k₀ δ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (hδ : |δ| < k₀)
    (V : ℝ →ᵇ ℝ) (hV : ‖V‖ < k₀ ^ 2 - δ ^ 2)
    (F : ℝ →ᵇ SpectralSpace ι) (i : ι) (hF : ∀ t, F t i = 0) :
    ∀ t, spectralPotentialInverse k hk₀ hk hδ V hV F t i = 0 := by
  let U := spectralPotentialInverse k hk₀ hk hδ V hV F
  let Ui := spectralCoordinateFunction U i
  have hr : 0 < k i + δ := by linarith [(abs_lt.mp hδ).1, hk i]
  have hs : 0 < k i - δ := by linarith [(abs_lt.mp hδ).2, hk i]
  have hiV : ‖V‖ < (k i + δ) * (k i - δ) := by
    have hkpos := hk₀.trans_le (hk i)
    nlinarith [hk i]
  have hsource : spectralCoordinateFunction (F - V • U) i = -(V * Ui) := by
    apply BoundedContinuousFunction.ext
    intro t
    change F t i - V t * U t i = -(V t * U t i)
    rw [hF, zero_sub]
  have heq : twoRateResolvent (k i + δ) (k i - δ) hr hs
      (spectralCoordinateFunction (F - V • U) i) = Ui := by
    apply BoundedContinuousFunction.ext
    intro t
    change twoRateInverse (k i + δ) (k i - δ) (fun y => (F - V • U) y i) t = U t i
    rw [← spectralConvolution_coordinate k hk₀ hk hδ (F - V • U) t i]
    exact congrArg (fun H : ℝ →ᵇ SpectralSpace ι => H t i)
      (spectralPotentialInverse_fixed k hk₀ hk hδ V hV F)
  have hn : ‖Ui‖ ≤ (‖V‖ * ‖Ui‖) / ((k i + δ) * (k i - δ)) := by
    calc
      ‖Ui‖ = ‖twoRateResolvent (k i + δ) (k i - δ) hr hs
          (spectralCoordinateFunction (F - V • U) i)‖ := congrArg norm heq.symm
      _ ≤ ‖spectralCoordinateFunction (F - V • U) i‖ / ((k i + δ) * (k i - δ)) :=
        twoRateResolvent_norm_le hr hs _
      _ ≤ (‖V‖ * ‖Ui‖) / ((k i + δ) * (k i - δ)) := by
        rw [hsource, norm_neg]
        exact div_le_div_of_nonneg_right (norm_mul_le V Ui) (mul_pos hr hs).le
  have hmul := (le_div_iff₀ (mul_pos hr hs)).mp hn
  have hz : ‖Ui‖ = 0 := by nlinarith [norm_nonneg Ui]
  have hu0 : Ui = 0 := norm_eq_zero.mp hz
  intro t
  exact congrArg (fun H : ℝ →ᵇ ℝ => H t) hu0

end Yamabe3.Analysis.Delaunay
