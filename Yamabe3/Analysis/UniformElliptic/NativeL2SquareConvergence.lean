import PoincareLib.Analysis.Elliptic.Regularity.WeakDerivativeLimit

/-!
# Actual L2 convergence from original square integrals

These three real L2 identities retain the original functions and measure.
Their proofs are the exact scalar Hilbert arguments previously written in
SmoothApproximationH1, isolated here without its unused local Caccioppoli
closure. The original broader module is unchanged. Distinct names avoid
redeclaring its constants if that module is imported later.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

theorem native_norm_toLp_sq_eq_integral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem native_norm_toLp_sub_sq_eq_integral_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← MemLp.toLp_sub hf hg]
  exact native_norm_toLp_sq_eq_integral_sq (hf.sub hg)

theorem native_tendsto_toLp_of_integral_sq_sub {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {uSeq : ℕ → X → ℝ} {u : X → ℝ}
    (hs : ∀ n, MemLp (uSeq n) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun n => ∫ x, (uSeq n x - u x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hs n).toLp (uSeq n)) atTop (𝓝 (hu.toLp u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 (ε ^ 2) (sq_pos_of_pos hε)] with n hn
  rw [dist_eq_norm]
  have hsquare := native_norm_toLp_sub_sq_eq_integral_sq (hs n) hu
  nlinarith [norm_nonneg ((hs n).toLp (uSeq n) - hu.toLp u)]

#check @native_norm_toLp_sq_eq_integral_sq
#check @native_norm_toLp_sub_sq_eq_integral_sq
#check @native_tendsto_toLp_of_integral_sq_sub
#print axioms native_norm_toLp_sq_eq_integral_sq
#print axioms native_norm_toLp_sub_sq_eq_integral_sq
#print axioms native_tendsto_toLp_of_integral_sq_sub

end Yamabe3.Analysis.UniformElliptic
