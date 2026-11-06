import Yamabe3.Analysis.NativeFullWeightedL2
import Yamabe3.Analysis.NativeDelaunayCompactH4Estimate

/-! A genuine same-source H2 to H4 estimate on any fixed interior
precompact region at time zero. The constant precedes orbit, phase, source, and time.
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

theorem exists_uniform_full_unweighted_H4_bound
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    {O V W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOO : closure O ⊆ ball (0:E) 1 \ {(0:E)})
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V)
    (a b : ℝ) (hVS : V ⊆ cylinderShell a b) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph), MemWkp 4 2 (actualWeightedFullModelField hκ0 hκ1 p f 0) W ∧
        iteratedWeakSobolevNorm 4 2 (actualWeightedFullModelField hκ0 hκ1 p f 0) W ≤ C*ENNReal.ofReal ‖f‖ := by
  obtain ⟨C₀,hC₀,h0⟩ := exists_full_weighted_shell_L2_bound hκ0 hκ1 a b
  obtain ⟨C₂,hC₂,h2⟩ := exists_uniform_weighted_source_precompact_bound hV hVc
    (fun x hx => by simpa only [mem_singleton_iff] using (hOO (subset_closure (hVO hx))).2)
    (R := 1) le_rfl
    (fun x hx => le_of_lt (by simpa only [mem_ball,dist_zero_right] using (hOO (subset_closure (hVO hx))).1))
  obtain ⟨C₄,hC₄,h4⟩ := exists_uniform_weak_delaunay_compact_H4_estimate hO
    (fun x hx => by simpa only [mem_singleton_iff] using (hOO (subset_closure hx)).2) hV hVc hVO hW hWc hWV
  refine ⟨C₄*(C₀+C₂),by finiteness,?_⟩
  intro p f
  have hscale : ∀ x ∈ closure O, Real.exp (-(0:ℝ)) • x ∈ ball (0:E) 1 \ {(0:E)} := by
    intro x hx
    simpa only [neg_zero,Real.exp_zero,one_smul] using hOO hx
  have huO := (fullModel_weighted_weakNegativeLaplacian hκ0 hκ1 p f 0 hO hOc hscale).1
  have huV := fullModel_weighted_weakNegativeLaplacian hκ0 hκ1 p f 0 hV hVc
    (fun x hx => hscale x (subset_closure (hVO hx)))
  have hF := h2 f 0 (by simp)
  have hL := h0 p f 0
  have hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, ∑ i : Fin 3, chosenWeakPartial' 2 i
        (actualWeightedFullModelField hκ0 hκ1 p f 0) V x * partialDeriv i φ x) =
      ∫ x in V, (actualWeightedSourceSlice f 0 x -
        annularDelaunayPotential p.orbit (p.phase+0) x*actualWeightedFullModelField hκ0 hκ1 p f 0 x)*φ x := by
    intro φ hφ hc hsφ
    rw [weakNegativeLaplacian_test_identity hV (huV.1.le_of_le (by omega)) φ hφ hc hsφ]
    apply integral_congr_ae
    exact huV.2.mul (EventuallyEq.refl _ _)
  have hh := h4 p.orbit p.smooth
    (fun t => ⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩) p.ode
    (p.phase+0) _ _ (locally_of_memWkp hO huO) hF.1 hweak
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hL0 : iteratedWeakSobolevNorm 0 2 (actualWeightedFullModelField hκ0 hκ1 p f 0) V ≤
      C₀*ENNReal.ofReal ‖f‖ := by
    rw [wkpNorm_zero]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hVS le_rfl)).trans hL.2
  calc
    _ ≤ C₄*(C₀*ENNReal.ofReal ‖f‖+C₂*ENNReal.ofReal ‖f‖) :=
      mul_le_mul le_rfl (add_le_add hL0 hF.2) zero_le zero_le
    _ = _ := by ring

#print axioms exists_uniform_full_unweighted_H4_bound
end Yamabe3.Analysis.UniformElliptic
