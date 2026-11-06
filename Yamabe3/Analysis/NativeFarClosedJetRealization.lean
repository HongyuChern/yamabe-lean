import Yamabe3.Analysis.NativeOriginalPhysicalFarSource
import Yamabe3.Analysis.NativeDensitySourceAlgebra

/-! Eliminate the auxiliary representative from the ACTUAL far
certificate by its proved same-curve identity. The physical source is
the literal closed-jet commutator, with the original returned element. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic.Iteration

 theorem nativeSupportedOuter_curve_physical_cutoff_jet
    (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2)
    (σ:AngularH1) (hσ:NativeAngularSpectralRegular (3/2) (angularEmbedding σ))
    {w:ℝ×S→ℝ} (hw:Measurable w)
    (hwcurve:∀t,(fun θ=>w (t,θ))=ᵐ[angularVolume](nativeSupportedOuterCurve b ht F d n σ t:S→ℝ))
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hs:∀x:E,x∉nativeSourceShell→∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0) (a s:ℝ):
    nativePhysicalShellSource a s (nativeCollarCutoffCommutatorCLM χ hχ
      (nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val)=ᵐ[volume]
      physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation s (cylinderLift w)) s a:=by
  obtain ⟨z,hz,hl,hzcurve,hzjet⟩:=exists_nativeSupportedOuter_same_curve_all_scale b ht F d n σ hσ
  have he:=native_lift_ae_eq_of_joint_slices hz hw (fun t=>(hzcurve t).trans (hwcurve t).symm)
  have hJ:(nativeSupportedOuterAllScaleJet b ht F d n σ hσ s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weightedPhysicalDilation s (cylinderLift w):=
    (hzjet s).1.trans (ae_mono (Measure.restrict_mono
      (subset_closure.trans nativeEntranceCollar_closure_subset_basic) le_rfl)
      (weightedPhysicalDilation_congr_ae he s))
  have hu:=nativeLocalH2_weighted_basicAnnulus (nativeOuter_same_curve_local_H2 b ht F d n σ hσ hw hwcurve) s
  exact nativeCollarCutoffCommutator_physical_identity χ hχ hs _ (hu.le_of_le (by norm_num:1≤2)) hJ a s

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

 theorem nativeActualFeedback_far_closed_jet_equation
    (X:nativeSupportedSourcePairSpace b) (η:H1Zero g.leviCivitaData univ):
    closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (W.R X).val η=
      ∫y,(nativeDensityCorrectedChartSource gE e (closedBall (0:E) R₀)
        (nativePhysicalShellSource a S (nativeCollarCutoffCommutatorCLM χout hχout
          (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X.val S).val)) y+
        (∑i:Fin n,nativeDensityCorrectedChartSource gE e (closedBall (0:E) R₀)
          (nativeOuterCutoffGeometricShell gE P hp v hv hb b ht a S (nativeOuterLogShellCenter (m+i.val)) χout hχout X.val) y)+
        8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y*
          toL2 g.leviCivitaData univ (W.R X).val y))*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure:=by
  obtain ⟨w,hw,hcurve,hweak⟩:=W.far X
  have hraw:=nativeSupportedOuter_curve_physical_cutoff_jet b ht X.val.2
    (nativeLowL2AngularCLM v hv hb X.val.1 0) (nativeFullL2NormalAngularCLM P hp v hv hb X.val.1)
    (nativeTwoSidedSourceSigmaCLM P hp v hv hb τ X.val)
    (nativeTwoSidedSourceSigma_regular P hp v hv hb τ X.val) hw hcurve χout hχout W.outer_derivatives a S
  have hn:=nativeDensitySource_congr_volume_ae g gE e he hei (K:=closedBall (0:E) R₀) measurableSet_closedBall hraw
  apply (hweak η).trans
  apply integral_congr_ae
  filter_upwards [hn] with y hy
  dsimp only [nativeSupportedTwoSidedExteriorAllScaleJet]
  rw [hy]

#print axioms nativeSupportedOuter_curve_physical_cutoff_jet
#print axioms nativeActualFeedback_far_closed_jet_equation
end Yamabe3.Analysis.SpherePolar
