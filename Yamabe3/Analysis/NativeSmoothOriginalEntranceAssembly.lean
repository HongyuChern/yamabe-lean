import Yamabe3.Analysis.NativeSmoothExteriorCollarSource
import Yamabe3.Analysis.NativeSourceJetEntranceBound
import Yamabe3.Analysis.NativeSmoothOriginalGlobalRealization
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

theorem exists_nativeSmoothOriginal_same_entrance_solution
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
    (χSm:E→ℝ) (hχone:∀x∈closedBall (0:E) 64,χSm x=1)
    (hSm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χSm))
    (T:H →L[ℝ] RH) (JSm:H →L[ℝ] H)
    (hJSm:∀z:H,JSm z=z+nativeRemoteReturnResponseCLM W (T (JSm z)))
    (hReal:NativeSmoothOriginalGlobalRealization hκ0 hκ1 p hp W T₀ Q₀ Rbase χSm hSm T JSm)
    {CSource:ℝ} (hCSource:0≤CSource)
    (hSource:‖nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm‖≤CSource):
    let Y:=nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm
    let Ji:=fun f=>nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale (T₀ f)+
      nativeTwoSidedInteriorJetCLM P hp v hv hb τ (Y f).val
    let Ko:=fun f=>nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0+
      nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht (Y f).val 0
    ∃(N:SpherePolar.S→Set E)(L:SpherePolar.S→(E→ℝ)→ₗ[ℝ](E→ℝ))(C:SpherePolar.S→ℝ≥0∞),
      (∀θ:SpherePolar.S,(θ:E)∈N θ ∧ IsOpen (N θ) ∧ IsCompact (closure (N θ)) ∧
        closure (N θ)⊆nativePoissonEntranceCollar ∧ C θ≠⊤) ∧
      ∀f:HalfEndPhysicalH2SourceGraph,
        let Z:=JSm (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f)
        ∃u:E→ℝ,Measurable u ∧
          (toL2 g.leviCivitaData univ Z:M→ℝ)=ᵐ[g.volumeMeasure.restrict
            (e '' euclideanDilatedDomain a (ball (0:E) 1))]coordinateExtension e (fun x:E=>u (a⁻¹ • x)) ∧
          MemWkpLocally 4 u (ball (0:E) 1\{0}) ∧
          (∀U:Set E,IsOpen U→IsCompact (closure U)→closure U⊆ball (0:E) 1\{0}→
            nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u=ᵐ[volume.restrict U]
              fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8) ∧
          (∀i:HalfEndPhysicalSliceIndex,
            ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T₀ f)+
              nativeTwoSidedAllScaleJetCLM P hp v hv hb τ i.val (Y f).val).val.1:E→ℝ)
                =ᵐ[volume.restrict nativePoissonEntranceCollar]
                  fun x=>Real.exp (3*i.val/2)*u (Real.exp (-i.val) • x)) ∧
          ∀θ:SpherePolar.S,
            MemWkp 4 2 (L θ (nativeCollarGluedFunction (Ji f).val.1 (Ko f).val.1)) (N θ) ∧
            iteratedWeakSobolevNorm 4 2 (L θ (nativeCollarGluedFunction (Ji f).val.1 (Ko f).val.1)) (N θ)≤
              C θ*ENNReal.ofReal ‖f‖ ∧
            (L θ (nativeCollarGluedFunction (Ji f).val.1 (Ko f).val.1)=ᵐ[volume.restrict (N θ∩ball (0:E) 1)]u):=by
  classical
  dsimp only
  let Ymap:=nativeFinalFeedbackSourceCLM W T₀ Q₀ Rbase T JSm
  let Jbase:=nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale
  let Jcorr:=nativeTwoSidedInteriorJetCLM P hp v hv hb τ
  let Kbase:=nativeH4MatchedExteriorJetCLM P ht
  let Kcorr:=nativeSupportedTwoSidedExteriorJetCLM P hp v hv hb b ht
  let CJ:=‖Jbase‖*‖T₀‖+‖Jcorr‖*CSource
  let CK:=‖Kbase‖*‖T₀‖+‖Kcorr‖*CSource
  have hCJ:0≤CJ:=by dsimp only [CJ];positivity
  have hCK:0≤CK:=by dsimp only [CK];positivity
  have hFam(θ:SpherePolar.S):=exists_nativeSourceJet_entrance_H4_bound gE a p.orbit p.smooth p.phase τ hCJ hCK (θ:E)
    (by simpa only [mem_sphere,dist_zero_right] using θ.property)
  choose N L C hθN hN hNc hND hC hReg using hFam
  refine ⟨N,L,C,fun θ=>⟨hθN θ,hN θ,hNc θ,hND θ,hC θ⟩,fun f=>?_⟩
  let Z₀:=nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f
  let Z:=JSm Z₀
  let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
  let Y₁:=nativeOriginalAffineFeedbackCLM W (0:RH →L[ℝ] nativeSupportedSourcePairSpace b) (ContinuousLinearMap.id ℝ RH) (T Z)
  let Y:=Y₀+Y₁
  let R:=Rbase (T₀ f)+T Z+W.R Y
  let J:=Jbase (T₀ f)+Jcorr Y.val
  let K:=nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) 0+
    nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht Y.val 0
  have hZ:Z=Q₀ f+nativeSupportedSignedEnergy W Y R:=
    (hJSm Z₀).trans (nativeOriginalPlusRemote_signed_identity W T₀ Q₀ Rbase f (T Z))
  have hFix:Y.val.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp gE a (T₀ f)+
      nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb τ gE a Y.val:=
    nativeOriginalPlusRemote_inner_source_fixed W Rbase (T₀ f) (T Z)
  obtain ⟨u,hum,hpot,hrep,hu,heq,hjet⟩:=nativeOriginalModelEnergy_supported_inner_source_with_jets
    hκ0 hκ1 p hp W hB hρ T₀ O L₀ Q₀ Y R hModel hQ₀ f hFix
  rw [←hZ] at hrep
  have hu4:=nativeOriginalSource_interior_H4 gE a p.orbit p.smooth p.phase f hu
    (fun U hU hUc hUO=>(heq U hU hUc hUO).2)
  have hJu:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u:=by
    simpa only [J,Jbase,Jcorr,nativeH4GraphZeroScale,mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul,
      nativeTwoSidedAllScale_zero] using hjet nativeH4GraphZeroScale
  have hY:‖Y.val‖≤CSource*‖f‖:=by
    change ‖Ymap f‖≤_
    exact Ymap.le_of_opNorm_le hSource f
  have hJ:‖J‖≤CJ*‖f‖:=by
    apply (norm_add_le _ _).trans
    exact (add_le_add ((Jbase.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (T₀.le_opNorm f) (norm_nonneg Jbase)))
      ((Jcorr.le_opNorm _).trans (mul_le_mul_of_nonneg_left hY (norm_nonneg Jcorr)))).trans_eq (by dsimp only [CJ];ring)
  have hK:‖K‖≤CK*‖f‖:=by
    dsimp only [K]
    rw [nativeH4MatchedExteriorAllScale_zero,nativeSupportedTwoSidedExteriorAllScale_zero_eq]
    apply (norm_add_le _ _).trans
    exact (add_le_add ((Kbase.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (T₀.le_opNorm f) (norm_nonneg Kbase)))
      ((Kcorr.le_opNorm _).trans (mul_le_mul_of_nonneg_left hY (norm_nonneg Kcorr)))).trans_eq (by dsimp only [CK];ring)
  have hc:=nativeSmoothOriginal_same_collar_realization hκ0 hκ1 p hp W hcoeff T₀ O L₀ Q₀ Rbase hModel hQ₀ T JSm hJSm f
  obtain ⟨C₀,C₁,hC₀,hC₁,Ft,hFt,hOuter,hRest⟩:=hReal f
  have hz:=nativeOriginal_computed_sources_zero_entrance W (T₀ f) Y₀ Y₁ C₀ C₁ hC₀ hC₁
  have ho:=nativeSmoothExterior_same_collar_equation W hcoeff χSm hχone J K Z C₀ C₁ Ft hz.1 hz.2 hFt hOuter hc.1
  refine ⟨u,hum,hrep,hu4,(fun U hU hUc hUO=>(heq U hU hUc hUO).2),hjet,fun θ=>?_⟩
  exact hReg θ f J K u hJ hK hc.2.1 hc.2.2.1 hJu
    (fun U hU hUc hUO=>(heq U hU hUc hUO).2) ho

#print axioms exists_nativeSmoothOriginal_same_entrance_solution
end Yamabe3.Analysis.SpherePolar
