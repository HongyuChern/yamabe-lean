import Yamabe3.Analysis.NativeSmoothPotentialResponseEquation
import Yamabe3.Analysis.NativeOriginalAffineInnerSource
import Yamabe3.Analysis.NativeOriginalAffineFeedback
import Yamabe3.Analysis.NativeH4InnerPartialFeedback
import Yamabe3.Analysis.NativeH4SupportedWindowSource

/-! The ACTUAL affine original-source feedback has the required inner
fixed point, since its incoming source has exactly zero first coordinate.
This discharges the partial inner cancellation premise without assuming
an obsolete full-collar exterior fixed point. -/
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


local notation "H" => H1Zero g.leviCivitaData univ
local notation "RH" => nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))

def nativeFinalFeedbackSourceCLM
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] RH)
    (T:H →L[ℝ] RH) (J:H →L[ℝ] H):HalfEndPhysicalH2SourceGraph →L[ℝ] nativeSupportedSourcePairSpace b:=
  (nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase).comp T₀+
    (nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH)).comp
      (T.comp (J.comp (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase)))

theorem nativeFinalFeedbackSourceCLM_apply
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] RH)
    (T:H →L[ℝ] RH) (J:H →L[ℝ] H) (f:HalfEndPhysicalH2SourceGraph):
    nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T J f=
      nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)+
      nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH)
        (T (J (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f))):=rfl

theorem nativeFinalFeedbackSourceCLM_uniform_bound
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] RH)
    (T:H →L[ℝ] RH) (J:H →L[ℝ] H)
    {CY CI C:ℝ} (hCY:0≤CY) (hCI:0≤CI) (hC:0≤C)
    (hY:‖nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase‖≤CY)
    (hI:‖W.I‖≤CI*Real.exp (-Real.log a/2)) (hT:‖T‖≤1/2) (hJ:‖J‖≤2)
    (hZ:‖nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase‖≤C*Real.sqrt a):
    ‖nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T J‖≤CY*‖T₀‖+4*CI*C:=by
  have hscale:Real.sqrt a*‖W.I‖≤CI:=by
    apply (mul_le_mul_of_nonneg_left hI (Real.sqrt_nonneg _)).trans_eq
    rw [←mul_assoc,mul_comm (Real.sqrt a) CI,mul_assoc]
    rw [show Real.sqrt a*Real.exp (-Real.log a/2)=1 by
      simpa only [mul_comm] using exp_negative_half_log_mul_sqrt ha,mul_one]
  apply (nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T J).opNorm_le_bound (by positivity)
  intro f
  let R:=T (J (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f))
  have hZf:‖nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f‖≤C*Real.sqrt a*‖f‖:=
    (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase).le_of_opNorm_le hZ f
  have hJf:‖J (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f)‖≤2*(C*Real.sqrt a*‖f‖):=
    (J.le_of_opNorm_le hJ _).trans (mul_le_mul_of_nonneg_left hZf (by norm_num))
  have hRf:‖R‖≤C*Real.sqrt a*‖f‖:=
    ((T.le_of_opNorm_le hT _).trans (mul_le_mul_of_nonneg_left hJf (by norm_num))).trans_eq (by ring)
  have hRemote:‖nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b)
      (ContinuousLinearMap.id ℝ RH) R‖≤(4*CI*C)*‖f‖:=by
    change ‖W.T (0-W.I R)‖≤_
    rw [zero_sub,map_neg,norm_neg]
    apply (W.T.le_of_opNorm_le W.feedback_bound _).trans
    apply (mul_le_mul_of_nonneg_left (W.I.le_opNorm R) (by norm_num:(0:ℝ)≤4)).trans
    rw [←mul_assoc]
    apply (mul_le_mul_of_nonneg_left hRf (by positivity:(0:ℝ)≤4*‖W.I‖)).trans
    calc
      _=(4*C*‖f‖)*(Real.sqrt a*‖W.I‖):=by ring
      _≤(4*C*‖f‖)*CI:=mul_le_mul_of_nonneg_left hscale (by positivity)
      _=_:=by ring
  have hBase:‖nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)‖≤
      CY*‖T₀‖*‖f‖:=
    ((nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase).le_of_opNorm_le hY _).trans
      ((mul_le_mul_of_nonneg_left (T₀.le_opNorm f) hCY).trans_eq (by ring))
  rw [nativeFinalFeedbackSourceCLM_apply]
  exact (norm_add_le _ _).trans ((add_le_add hBase hRemote).trans_eq (by ring))

#print axioms nativeFinalFeedbackSourceCLM_apply
#print axioms nativeFinalFeedbackSourceCLM_uniform_bound
end Yamabe3.Analysis.SpherePolar
