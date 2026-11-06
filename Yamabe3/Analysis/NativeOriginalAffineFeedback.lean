import Yamabe3.Analysis.NativeActualFeedbackEnergyBundle
import Yamabe3.Analysis.NativeH4SupportedWindowSource

/-! Exact affine source algebra for an original-H4 baseline. The near
residual below is an actual producer. A baseline far return remains an
EXPLICIT INTERMEDIATE input to this composition lemma, not a proved
physical producer merely by definition. The full native PDE is separate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
  {P:NativeHighPotential}
  {hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ}
  {v:ℝ→ℝ} {hv:Continuous v} {hb:∀t,0 ≤ v t ∧ v t ≤ 1}
  {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
    (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
    (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
    (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1)

variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def nativeOriginalAffineFeedbackCLM
    (B₀:X →L[ℝ] nativeSupportedSourcePairSpace b)
    (R₀:X →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) :
    X →L[ℝ] nativeSupportedSourcePairSpace b :=
  W.T.comp (B₀-W.I.comp R₀)

def nativeOriginalAffineReturnCLM
    (B₀:X →L[ℝ] nativeSupportedSourcePairSpace b)
    (R₀:X →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) :
    X →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)) :=
  R₀+W.R.comp (nativeOriginalAffineFeedbackCLM W B₀ R₀)

theorem nativeOriginalAffineFeedback_fixed
    (B₀:X →L[ℝ] nativeSupportedSourcePairSpace b)
    (R₀:X →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) (x:X) :
    (nativeOriginalAffineFeedbackCLM W B₀ R₀ x).val=(B₀ x).val+
      nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a (nativeOriginalAffineFeedbackCLM W B₀ R₀ x).val-
      (W.I (nativeOriginalAffineReturnCLM W B₀ R₀ x)).val := by
  have hh:=W.source_fixed ((B₀-W.I.comp R₀) x)
  change (nativeOriginalAffineFeedbackCLM W B₀ R₀ x).val=
    (B₀ x-W.I (R₀ x)).val+
      nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a (nativeOriginalAffineFeedbackCLM W B₀ R₀ x).val+
      -(W.I (W.R (nativeOriginalAffineFeedbackCLM W B₀ R₀ x))).val at hh
  change _=(B₀ x).val+_-(W.I (R₀ x+W.R (nativeOriginalAffineFeedbackCLM W B₀ R₀ x))).val
  rw [map_add]
  change _=(B₀ x).val+_-((W.I (R₀ x)).val+(W.I (W.R (nativeOriginalAffineFeedbackCLM W B₀ R₀ x))).val)
  apply hh.trans
  change (B₀ x).val-(W.I (R₀ x)).val+_+_= _
  abel

theorem nativeOriginalAffineFeedback_norm
    (B₀:X →L[ℝ] nativeSupportedSourcePairSpace b)
    (R₀:X →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) :
    ‖nativeOriginalAffineFeedbackCLM W B₀ R₀‖ ≤ 4*(‖B₀‖+‖W.I‖*‖R₀‖) := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right W.feedback_bound (norm_nonneg _)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num:(0:ℝ) ≤ 4)
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le _ _))

def nativeActualH4BaselineResidualCLM : HalfEndPhysicalH4Graph →L[ℝ] nativeSupportedSourcePairSpace b :=
  nativeH4SupportedWindowSourceCLM P hp ht m gE a b W.near_support

theorem nativeActualH4BaselineResidual_val (x:HalfEndPhysicalH4Graph) :
    (nativeActualH4BaselineResidualCLM W x).val=nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a x := rfl

#print axioms nativeOriginalAffineFeedback_fixed
#print axioms nativeOriginalAffineFeedback_norm
#print axioms nativeActualH4BaselineResidual_val
end Yamabe3.Analysis.SpherePolar
