import Yamabe3.Analysis.NativeOriginalWeightedEquation
import Yamabe3.Analysis.NativeUniformWeakH4Estimate
import Yamabe3.Analysis.NativeCollarJetSobolevBound

/-! Uniform weighted interior H4 from the same original native source
and the actual all-scale collar jet. Neither a new field nor a substituted
source is selected. The estimate precedes scale, orbit, phase and source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open Poincare.Analysis.Elliptic.Iteration
local notation "H" => (Metric.ball (0:E) 1 \ {(0:E)})

theorem exists_native_original_weighted_H4_bound
    (g : RiemannianMetric 3 E) (hB : g.euclideanCoefficients 0=innerSL ℝ)
    (hρ : g.pullbackVolumeDensity id 0=1)
    {O V W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hO0 : ∀x∈closure O,x≠0) (hOR : ∀x∈closure O,‖x‖ ≤ 2)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hVD : V ⊆ nativePoissonEntranceCollar)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃δ : ℝ,0<δ ∧ ∃C : ℝ≥0∞,C≠⊤ ∧ ∀ε : ℝ,0 ≤ ε → ε<δ →
      ∀v : ℝ→ℝ,ContDiff ℝ ∞ v →
      (∀t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀t,deriv (deriv v) t=radialForce (v t)) →
      ∀(phase : ℝ) (f : HalfEndPhysicalH2SourceGraph) (u : E→ℝ),MemWkpLocally 4 u H →
      (∀U : Set E,IsOpen U → IsCompact (closure U) → closure U ⊆ H →
        nativeWeakRescaledDelaunayJacobian U g ε v phase u=ᵐ[volume.restrict U]
          (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8)) →
      ∀s : ℝ,Real.log 2+1 ≤ s → ∀J : nativeCollarJetClosure,
      ((J.val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))) →
      MemWkp 4 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) W ∧
      iteratedWeakSobolevNorm 4 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) W ≤ 
        C*(ENNReal.ofReal ‖J‖+ENNReal.ofReal ‖f‖) := by
  obtain ⟨C₂,hC₂,hsource⟩ := exists_uniform_weighted_source_precompact_bound hV hVc
    (fun x hx => hO0 x (subset_closure (hVO hx))) (by norm_num : (1:ℝ) ≤ 2)
    (fun x hx => hOR x (subset_closure (hVO hx)))
  obtain ⟨δ,hδ,C₄,hC₄,hestimate⟩ := exists_uniform_native_weak_H4_estimate g hB hρ hO
    (fun x hx => hO0 x (subset_closure hx)) hV hVc hVO
    (fun x hx => nativeEntranceCollar_annular (hVD hx)) hW hWc hWV
  refine ⟨δ,hδ,C₄*(1+C₂),by finiteness,?_⟩
  intro ε hε hεδ v hv hb hODE phase f u hu he s hs J hJ
  have hs0 : 0 ≤ s := by have hh := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2);linarith
  have hscale : ∀x∈closure O,Real.exp (-s) • x∈H := by
    intro x hx
    have hsmall : Real.exp (-s)*2<1 := by
      rw [show (2:ℝ)=Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,←Real.exp_add,Real.exp_lt_one_iff]
      linarith
    refine ⟨?_,?_⟩
    · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_left (hOR x hx) (Real.exp_pos _).le).trans_lt hsmall
    · simpa only [mem_singleton_iff] using smul_ne_zero (Real.exp_pos (-s)).ne' (hO0 x hx)
  have huO := (nativeOriginalSource_weighted_weakJacobian g ε v phase f hu he s hO hOc hscale).1
  have huV := nativeOriginalSource_weighted_weakJacobian g ε v phase f hu he s hV hVc
    (fun x hx => hscale x (subset_closure (hVO hx)))
  have hF := hsource f s (by linarith)
  have hr : ε*Real.exp (-s)<δ :=
    (mul_le_of_le_one_right hε (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs0))).trans_lt hεδ
  have hh := hestimate (ε*Real.exp (-s)) (mul_nonneg hε (Real.exp_pos _).le) hr v hv hb hODE
    (phase+s) _ _ (locally_of_memWkp hO huO) hF.1 huV.2
  have hL0 : iteratedWeakSobolevNorm 0 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) V ≤ ENNReal.ofReal ‖J‖ := by
    rw [wkpNorm_zero,←eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset hVD hJ)]
    apply (eLpNorm_mono_measure _ (Measure.restrict_mono hVD le_rfl)).trans
    rw [←Lp.enorm_def,←ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    change ‖J.val.1‖ ≤ ‖J.val‖
    rw [Prod.norm_def]
    exact le_max_left _ _
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _  ≤  C₄*(ENNReal.ofReal ‖J‖+C₂*ENNReal.ofReal ‖f‖) := mul_le_mul le_rfl (add_le_add hL0 hF.2) zero_le zero_le
    _  ≤  C₄*((1+C₂)*ENNReal.ofReal ‖J‖+(1+C₂)*ENNReal.ofReal ‖f‖) := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      apply add_le_add
      · exact le_mul_of_one_le_left zero_le (le_add_right le_rfl)
      · exact mul_le_mul (le_add_left le_rfl) le_rfl zero_le zero_le
    _ = _ := by rw [←mul_add,mul_assoc]

#print axioms exists_native_original_weighted_H4_bound
end Yamabe3.Analysis.UniformElliptic
