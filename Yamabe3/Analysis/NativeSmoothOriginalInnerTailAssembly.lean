import Yamabe3.Analysis.NativeOriginalSupportedInnerJets
import Yamabe3.Analysis.NativeFinalFeedbackSourceMap
import Yamabe3.Analysis.NativeCorrectedInteriorH4
import Yamabe3.Analysis.NativeOriginalPlusRemoteSource
import Yamabe3.Analysis.NativeScaledInnerWeakEquation
import Yamabe3.Analysis.NativeOriginalSupportedInnerSource
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


local notation "H" => H1Zero g.leviCivitaData univ
local notation "RH" => nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))

theorem exists_nativeSmoothOriginal_same_inner_tail_solution
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] RH)
    (hModel:NativeOriginalModelEnergyRealization hκ0 hκ1 p hp ht χout S O T₀ L₀)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (T:H →L[ℝ] RH) (JSm:H →L[ℝ] H)
    (hJSm:∀z:H,JSm z=z+nativeRemoteReturnResponseCLM W (T (JSm z)))
    (CSource:ℝ) (Htail:ℝ≥0∞)
    (hSource:‖nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm‖≤CSource)
    (hTail:∀(f:HalfEndPhysicalH2SourceGraph)(Y:NativeTwoSidedSource)(u:E→ℝ),
      ‖Y‖≤CSource*‖f‖→MemWkpLocally 4 u (ball (0:E) 1\{0})→
      (∀U:Set E,IsOpen U→IsCompact (closure U)→closure U⊆ball (0:E) 1\{0}→
        nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u
          =ᵐ[volume.restrict U]fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8)→
      (∀i:HalfEndPhysicalSliceIndex,
        ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T₀ f)+
          nativeTwoSidedAllScaleJetCLM P hp v hv hb τ i.val Y).val.1:E→ℝ)
          =ᵐ[volume.restrict nativePoissonEntranceCollar]
            fun x=>Real.exp (3*i.val/2)*u (Real.exp (-i.val) • x))→
      ∀s:ℝ,4≤ s→MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus≤Htail*ENNReal.ofReal ‖f‖)
    (f:HalfEndPhysicalH2SourceGraph):
    let Z:=JSm (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f)
    ∃u:E→ℝ,Measurable u ∧
      MemLp (fun x=>nativeHalfEndPotentialCoefficient p.potential x*u x) 2
        (volume.restrict (ball (0:E) 1\{0})) ∧
      (toL2 g.leviCivitaData univ Z:M→ℝ)=ᵐ[g.volumeMeasure.restrict
        (e '' euclideanDilatedDomain a (ball (0:E) 1))]
          coordinateExtension e (fun x:E=>u (a⁻¹ • x)) ∧
      MemWkpLocally 2 u (ball (0:E) 1\{0}) ∧
      MemWkpLocally 4 u (ball (0:E) 1\{0}) ∧
      (∀s:ℝ,4≤ s→MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus≤Htail*ENNReal.ofReal ‖f‖) ∧
      (∀U:Set E,IsOpen U → IsCompact (closure U) → closure U⊆ball (0:E) 1\{0} →
        MemWkp 2 2 u U ∧ nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u
          =ᵐ[volume.restrict U]fun y=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) y/8) ∧
      ∃F_E:Lp ℝ 2 (volume:Measure E),
        (F_E:E→ℝ)=ᵐ[volume](euclideanDilatedDomain a (ball (0:E) 1)).indicator
          (fun x=>gE.pullbackVolumeDensity id x*nativeScaledEffectiveSource gE a
            (halfEndPhysicalH2SourceGraphValue f) p.potential u x) ∧
        let F:=nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hsource F_E
        (Z,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const
          (e '' euclideanDilatedDomain a (ball (0:E) 1)) ∧
        (Z,F)∈NativeWeakEllipticDataSpace g (e '' euclideanDilatedDomain a (ball (0:E) 1))
          (nativeJacobianPotential g (fun _:M=>0)) (nativeJacobianPotential_smooth g contMDiff_const):=by
  dsimp only
  let Z₀:=nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f
  let Z:=JSm Z₀
  let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  let Y₁:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) (T Z)
  let Y:=Y₀+Y₁
  let R:=Rbase (T₀ f)+T Z+W.R Y
  have hZ:Z=Q₀ f+nativeSupportedSignedEnergy W Y R:=
    (hJSm Z₀).trans (nativeOriginalPlusRemote_signed_identity W T₀ Q₀ Rbase f (T Z))
  have hFix:Y.val.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp gE a (T₀ f)+
      nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a Y.val:=
    nativeOriginalPlusRemote_inner_source_fixed W Rbase (T₀ f) (T Z)
  obtain ⟨u,hum,hpot,hrep,hu,heq,hjet⟩:=nativeOriginalModelEnergy_supported_inner_source_with_jets
    hκ0 hκ1 p hp W hB hρ T₀ O L₀ Q₀ Y R hModel hQ₀ f hFix
  rw [←hZ] at hrep
  have hY:‖Y.val‖≤CSource*‖f‖:=by
    change ‖nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm f‖≤_
    exact (nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm).le_of_opNorm_le hSource f
  have hReg:=nativeOriginalSource_interior_H4 gE a p.orbit p.smooth p.phase f hu
    (fun U hU hUc hUO=>(heq U hU hUc hUO).2)
  have hTailActual:=hTail f Y.val u hY hReg (fun U hU hUc hUO=>(heq U hU hUc hUO).2) hjet
  have hR₀:0<R₀:=by linarith [W.receiving_fit]
  obtain ⟨F_E,hFE,hweak⟩:=nativeScaledInner_same_field_weak_equation g gE e he hei hR₀ hsource
    hcoeff p ha (nativeActualFeedback_inner_ball_fit W) (halfEndPhysicalH2SourceGraphValue f) u hum hpot Z hrep heq
  exact ⟨u,hum,hpot,hrep,hu,hReg,hTailActual,heq,F_E,hFE,hweak,
    nativeForcedEnergySpace_mem_data g (fun _:M=>0) contMDiff_const _ _ _ hweak⟩

#print axioms exists_nativeSmoothOriginal_same_inner_tail_solution
end Yamabe3.Analysis.SpherePolar
