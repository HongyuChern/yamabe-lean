import Yamabe3.Analysis.NativeH4ValueInnerEquation
import Yamabe3.Analysis.NativeBaselineSupportedIdentity
import Yamabe3.Analysis.NativeOriginalAffineOriginalSource
import Yamabe3.Analysis.NativeOriginalSignedInnerIdentity
import Yamabe3.Analysis.NativeOriginalModelEnergyRealization
import Yamabe3.Analysis.NativeWeightedFieldPotentialL2
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
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
variable {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
local notation "P" => p.nativeHighPotential hκ0 hκ1
local notation "v" => (fun t=>p.orbit (t+p.phase))
local notation "hv" => (p.smooth.continuous.comp (continuous_id.add continuous_const))
local notation "hb" => (fun t=>p.bounded (t+p.phase))
variable   {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle g gE e he hei R₀ hsource
    (p.nativeHighPotential hκ0 hκ1) hp (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) τ cTail ht m n b S CR CM χin χout hχin hχout a ha ha1)


theorem nativeOriginalModelEnergy_supported_inner_source_with_jets
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Y:nativeSupportedSourcePairSpace b)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (hmodel:NativeOriginalModelEnergyRealization hκ0 hκ1 p hp ht χout S O T₀ L₀)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (f:HalfEndPhysicalH2SourceGraph)
    (hFix:Y.val.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp gE a (T₀ f)+
      nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a Y.val) :
    ∃u:E→ℝ,Measurable u ∧
      MemLp (fun x=>nativeHalfEndPotentialCoefficient p.potential x*u x) 2
        (volume.restrict (ball (0:E) 1\{0})) ∧
      (toL2 g.leviCivitaData univ (Q₀ f+nativeSupportedSignedEnergy W Y R):M→ℝ)
        =ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a (ball (0:E) 1))]
          coordinateExtension e (fun x:E=>u (a⁻¹ • x)) ∧
      MemWkpLocally 2 u (ball (0:E) 1\{0}) ∧
      (∀U:Set E,IsOpen U → IsCompact (closure U) → closure U⊆ball (0:E) 1\{0} →
        MemWkp 2 2 u U ∧ nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u
          =ᵐ[volume.restrict U]fun y=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) y/8) ∧
      ∀i:HalfEndPhysicalSliceIndex,
        ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T₀ f)+
          nativeTwoSidedAllScaleJetCLM P hp v hv hb τ i.val Y.val).val.1:E→ℝ)
          =ᵐ[volume.restrict nativePoissonEntranceCollar]
            fun y=>Real.exp (3*i.val/2)*u (Real.exp (-i.val) • y) := by
  obtain ⟨F,hF2,hTF,hFa,qi,wo,hqi,hwo,hbi,hbo,hLE⟩:=hmodel f
  obtain ⟨wi,wc,hwi,hwc,hci,hco,hZ⟩:=nativeBaselineSupportedSigned_inner_identity W T₀ Q₀ Y R O L₀ hQ₀ f F qi wo hLE
  let u:E→ℝ:=fun x=>F x+cylinderLift qi x+cylinderLift wi x
  have hFm:Measurable F:=hF2.continuousOn.measurable_of_countable_compl (by
    simpa only [compl_compl] using countable_singleton (0:E))
  have hum:Measurable u:=(hFm.add (measurable_cylinderLift hqi)).add (measurable_cylinderLift hwi)
  have hjet(i:HalfEndPhysicalSliceIndex):
      ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T₀ f)+
        nativeTwoSidedAllScaleJetCLM P hp v hv hb τ i.val Y.val).val.1:E→ℝ)
        =ᵐ[volume.restrict nativePoissonEntranceCollar]
          fun y=>Real.exp (3*i.val/2)*u (Real.exp (-i.val) • y):=by
    have hi:=hci i.val
    let J:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T₀ f)
    let K:=nativeTwoSidedAllScaleJetCLM P hp v hv hb τ i.val Y.val
    have hs:=Lp.coeFn_add J.val.1 K.val.1
    filter_upwards [hbi i,hi,hs] with y hbase hi hs
    change ((J.val.1+K.val.1:NativeCollarL2):E→ℝ) y=_
    rw [hs]
    change (J.val.1:E→ℝ) y+(K.val.1:E→ℝ) y=_
    change (J.val.1:E→ℝ) y=Real.exp (3*i.val/2)*(F (Real.exp (-i.val) • y)+cylinderLift qi (Real.exp (-i.val) • y)) at hbase
    change (K.val.1:E→ℝ) y=Real.exp (3*i.val/2)*cylinderLift wi (Real.exp (-i.val) • y) at hi
    rw [hbase,hi]
    dsimp only [u]
    ring
  have hlocal:=nativeH4ValueCorrected_local_source_identity hκ0 hκ1 p hp b ht ({()}:Finset Unit)
    (fun _=>gE) (fun _ _=>hB) (fun _ _=>hρ) a ha.le ha1 () (by simp) (T₀ f) Y.val hFix F u hTF hjet
  have heq:MemWkpLocally 2 u (ball (0:E) 1\{0}) ∧
      ∀U:Set E,IsOpen U → IsCompact (closure U) → closure U⊆ball (0:E) 1\{0} →
        MemWkp 2 2 u U ∧ nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u
          =ᵐ[volume.restrict U]fun y=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) y/8:=by
    refine ⟨hlocal.1,fun U hU hUc hUO=>?_⟩
    obtain ⟨huU,hOp⟩:=hlocal.2 U hU hUc hUO
    exact ⟨huU,hOp.trans (nativeOriginalModel_flat_same_source hκ0 hκ1 p f F hFa hU hUc hUO).2⟩
  obtain ⟨D₀,hD₀,h₀⟩:=exists_nativeH4MatchedScale_bound (fullBubbleHighPotential (-τ)) P hp
  obtain ⟨D₁,hD₁,h₁⟩:=exists_nativeTwoSidedAllScale_bound P hp v hv hb τ
  let J:ℕ→nativeCollarJetClosure:=fun n=>
    nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp
      (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n)) (T₀ f)+
    nativeTwoSidedAllScaleJetCLM P hp v hv hb τ (nativeLogShellCenter n) Y.val
  let C:=D₀*‖T₀ f‖+D₁*‖Y.val‖
  have hC:0≤C:=by dsimp only [C];positivity
  have hJbound(n:ℕ):‖J n‖≤C:=by
    have h0:= (nativeH4MatchedScaleRawJetCLM (fullBubbleHighPotential (-τ)) P hp
      (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n))).le_of_opNorm_le
        (h₀ (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n))) (T₀ f)
    have h1:= (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb τ (nativeLogShellCenter n)).le_of_opNorm_le
      (h₁ (nativeLogShellCenter n)) Y.val
    exact (norm_add_le _ _).trans (add_le_add h0 h1)
  have hpot:=native_weighted_field_potential_memLp J u hum
    (fun n=>hjet (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n))) hC hJbound p.potential
  exact ⟨u,hum,hpot,hZ,heq.1,heq.2,hjet⟩

#print axioms nativeOriginalModelEnergy_supported_inner_source_with_jets
end Yamabe3.Analysis.SpherePolar
