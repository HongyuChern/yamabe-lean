import Yamabe3.Analysis.NativeActualIncomingCoreIdentity
import Yamabe3.Analysis.NativeCoreSourcePhysicalPairing
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


theorem nativeActualIncoming_core_operator_cancellation
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))):
    ∃F:E→ℝ,ContDiff ℝ ∞ F ∧HasCompactSupport F ∧
      (∀x∈closedBall (0:E) 4,F=ᶠ[𝓝 x]
        (fun y=>nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const W.open_domain R (e (a • y)))) ∧
      ∃ψ:EnergyTest g.leviCivitaData univ,
        (ψ:H1Zero g.leviCivitaData univ)=
          energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val ∧
        (ψ:M→ℝ)=coordinateExtension e (fun x:E=>χin (a⁻¹ • x)*F (a⁻¹ • x)) ∧
        ∀(η:EnergyTest g.leviCivitaData univ)(φ:E→ℝ)
          (hφ:ContDiff ℝ ∞ φ)(hc:HasCompactSupport φ)(h0:(0:E)∉tsupport φ),
          (∀x∈closedBall (0:E) (7/2:ℝ),φ x=η (e (a • x))) →
          closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
            (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val)
            (η:H1Zero g.leviCivitaData univ)+
            8*a*inner ℝ (W.I R).val.2 (nativePhysicalPairTestL2 φ hφ hc h0)=
              8*a*(∫x in ball (0:E) (Real.exp cTail+1),nativeIncomingPotentialCoefficient gE a τ cTail χin x*
                toL2 g.leviCivitaData univ R.val (e (a • x))*φ x):=by
  obtain ⟨F,hF,hFc,hrep,hreg,hzero,hI⟩:=exists_nativeActualIncoming_same_core_source_identity W hcoeff R
  obtain ⟨ψ,hψH,hcoord,hop,Fcore,hFcore,hweak⟩:=
    nativeActualCore_same_completed_operator_source W hcoeff R F hF hrep
  refine ⟨F,hF,hFc,hrep,ψ,hψH,hcoord,fun η φ hφ hc h0 htest=>?_⟩
  have hfit4:euclideanDilatedDomain a (ball (0:E) 4)⊆closedBall (0:E) R₀:=by
    apply euclideanDilatedBall_subset_closedBall ha
    have hh:=W.receiving_fit
    linarith
  have hphys:=nativeCore_actual_source_physical_pairing g gE e he hei hsource hcoeff ha hfit4
    χin F W.inner_compact W.inner_support W.inner_plateau hzero ψ hcoord hop η φ htest
  have hcore:closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
      (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val)
      (η:H1Zero g.leviCivitaData univ)=
      ∫y,(-8*g.leviCivitaData.laplacian ψ y+g.leviCivitaData.scalarCurvature y*ψ y)*η y ∂g.volumeMeasure:=by
    rw [hweak,L2.inner_def,toL2_coe]
    apply integral_congr_ae
    filter_upwards [hFcore,η.memLp.coeFn_toLp] with y hf hy
    simp only [Real.inner_apply]
    change (Fcore:M→ℝ) y*(η.memLp.toLp η) y=_
    rw [hf,hy]
  rw [hcore,hphys,hI φ hφ hc h0]
  ring

#print axioms nativeActualIncoming_core_operator_cancellation
end Yamabe3.Analysis.SpherePolar
