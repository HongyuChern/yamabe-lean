import Yamabe3.Analysis.NativeIncomingCoreSourcePairing
import Yamabe3.Analysis.NativeActualIncomingLocalEquation
import Yamabe3.Analysis.NativeHomogeneousH4Return
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
open SphereSpectrum Delaunay UniformElliptic GreenParametrix PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
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


theorem exists_nativeActualIncoming_same_core_source_identity
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))):
    ∃F:E→ℝ,ContDiff ℝ ∞ F ∧HasCompactSupport F ∧
      (∀x∈closedBall (0:E) 4,F=ᶠ[𝓝 x]
        (fun y=>nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const W.open_domain R (e (a • y)))) ∧
      EqOn (regularLowH4Field (W.J R)) F (closedBall (0:E) 4) ∧
      (∀x∈closedBall (0:E) 4,
        principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x+
          a^2*nativePotentialDensity gE (a • x)*F x=0) ∧
      ∀(φ:E→ℝ)(hφ:ContDiff ℝ ∞ φ)(hc:HasCompactSupport φ)(h0:(0:E)∉tsupport φ),
        inner ℝ (W.I R).val.2 (nativePhysicalPairTestL2 φ hφ hc h0)=
          (∫x in ball (0:E) (Real.exp cTail+1),nativeIncomingPotentialCoefficient gE a τ cTail χin x*
            toL2 g.leviCivitaData univ R.val (e (a • x))*φ x)-
          (∫x:E,nativeCoreUnitOperator gE a χin F x*φ x):=by
  obtain ⟨F,hF,hFc,he,hreg⟩:=exists_nativeActualIncoming_same_smooth_field W R
  have hzero(x:E)(hx:x∈closedBall (0:E) 4):
      principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x+
        a^2*nativePotentialDensity gE (a • x)*F x=0:=
    nativeActualIncoming_smooth_local_operator_zero W hcoeff R F hF he hx
  refine ⟨F,hF,hFc,he,hreg,hzero,fun φ hφ hc h0=>?_⟩
  have hi:=congrArg Prod.snd (W.incoming.2.1 R)
  change (W.I R).val.2=W.U R.val+nativeIncomingCommutatorSourceCLM gE a χin hχin (W.J R) at hi
  rw [hi,inner_add_left,W.incoming.2.2 R φ hφ hc h0,
    nativeIncomingCommutatorSource_eq_negative_core_test gE a χin hχin W.inner_support W.inner_plateau
      (W.J R) F hF hreg hzero φ hφ hc h0]
  rfl

#print axioms exists_nativeActualIncoming_same_core_source_identity
end Yamabe3.Analysis.SpherePolar
