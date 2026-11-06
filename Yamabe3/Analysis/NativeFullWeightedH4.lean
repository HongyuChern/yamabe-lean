import Yamabe3.Analysis.NativeFullWeightedL2
import Yamabe3.Analysis.NativeDelaunayCompactH4Estimate

/-! A genuine same-source weighted H2 to H4 estimate for all sufficiently
positive times. The constant precedes orbit, phase, source, and time.
The original field satisfies the scaled equation; none is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_full_weighted_H4_bound
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    {O V W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hO0 : ∀ x ∈ closure O, x ≠ 0) {R : ℝ} (hR : 1 ≤ R)
    (hOR : ∀ x ∈ closure O, ‖x‖ ≤ R)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V)
    (a b : ℝ) (hVS : V ⊆ cylinderShell a b) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph) (s : ℝ),
      Real.log R+1 ≤ s → MemWkp 4 2 (actualWeightedFullModelField hκ0 hκ1 p f s) W ∧
        iteratedWeakSobolevNorm 4 2 (actualWeightedFullModelField hκ0 hκ1 p f s) W ≤ C*ENNReal.ofReal ‖f‖ := by
  obtain ⟨C₀,hC₀,h0⟩ := exists_full_weighted_shell_L2_bound hκ0 hκ1 a b
  obtain ⟨C₂,hC₂,h2⟩ := exists_uniform_weighted_source_precompact_bound hV hVc
    (fun x hx => hO0 x (subset_closure (hVO hx))) hR
    (fun x hx => hOR x (subset_closure (hVO hx)))
  obtain ⟨C₄,hC₄,h4⟩ := exists_uniform_weak_delaunay_compact_H4_estimate hO
    (fun x hx => hO0 x (subset_closure hx)) hV hVc hVO hW hWc hWV
  refine ⟨C₄*(C₀+C₂),by finiteness,?_⟩
  intro p f s hs
  have hscale : ∀ x ∈ closure O, Real.exp (-s) • x ∈ ball (0:E) 1 \ {(0:E)} := by
    intro x hx
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have he : Real.exp (-s)*R = Real.exp (Real.log R-s) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hRpos]
      ring
    have hsmall : Real.exp (-s)*R < 1 := by
      rw [he,Real.exp_lt_one_iff]
      linarith
    refine ⟨?_,?_⟩
    · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_left (hOR x hx) (Real.exp_pos _).le).trans_lt hsmall
    · simpa only [mem_singleton_iff] using smul_ne_zero (Real.exp_pos (-s)).ne' (hO0 x hx)
  have huO := (fullModel_weighted_weakNegativeLaplacian hκ0 hκ1 p f s hO hOc hscale).1
  have huV := fullModel_weighted_weakNegativeLaplacian hκ0 hκ1 p f s hV hVc
    (fun x hx => hscale x (subset_closure (hVO hx)))
  have hF := h2 f s (by linarith)
  have hL := h0 p f s
  have hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, ∑ i : Fin 3, chosenWeakPartial' 2 i
        (actualWeightedFullModelField hκ0 hκ1 p f s) V x * partialDeriv i φ x) =
      ∫ x in V, (actualWeightedSourceSlice f s x -
        annularDelaunayPotential p.orbit (p.phase+s) x*actualWeightedFullModelField hκ0 hκ1 p f s x)*φ x := by
    intro φ hφ hc hsφ
    rw [weakNegativeLaplacian_test_identity hV (huV.1.le_of_le (by omega)) φ hφ hc hsφ]
    apply integral_congr_ae
    exact huV.2.mul (EventuallyEq.refl _ _)
  have hh := h4 p.orbit p.smooth
    (fun t => ⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩) p.ode
    (p.phase+s) _ _ (locally_of_memWkp hO huO) hF.1 hweak
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hL0 : iteratedWeakSobolevNorm 0 2 (actualWeightedFullModelField hκ0 hκ1 p f s) V ≤
      C₀*ENNReal.ofReal ‖f‖ := by
    rw [wkpNorm_zero]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hVS le_rfl)).trans hL.2
  calc
    _ ≤ C₄*(C₀*ENNReal.ofReal ‖f‖+C₂*ENNReal.ofReal ‖f‖) :=
      mul_le_mul le_rfl (add_le_add hL0 hF.2) zero_le zero_le
    _ = _ := by ring

#print axioms exists_uniform_full_weighted_H4_bound
end Yamabe3.Analysis.UniformElliptic
