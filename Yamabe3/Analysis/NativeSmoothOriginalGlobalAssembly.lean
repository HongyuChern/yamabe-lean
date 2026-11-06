import Yamabe3.Analysis.NativeCorrectedInteriorH4
import Yamabe3.Analysis.NativeSmoothOriginalExteriorAssembly
import Yamabe3.Analysis.NativeSmoothOriginalInnerAssembly
import Yamabe3.Analysis.NativeSmoothOriginalCollarAssembly
import Yamabe3.Analysis.NativeChartSphereRegions
import Yamabe3.Analysis.NativeGlobalConormalBalance
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
open scoped NNReal Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
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


 theorem exists_nativeSmoothOriginal_same_global_solution
    (hY:0<Target.yamabeConstant g)
    (χSm:E→ℝ) (hSm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χSm))
    (q:Lp ℝ (3/2:ℝ≥0∞) g.volumeMeasure)
    (hq:(q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y-
      nativeScaledSmoothBubblePotential e τ a χSm y))
    (T:(H1Zero g.leviCivitaData univ) →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (hTw:∀z:H1Zero g.leviCivitaData univ,∀η:H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const (T z).val η=
        ∫y,(nativeCriticalPotentialReactionCLM g hY q z y+8*(nativeCompactChartFunction e (closedBall (0:E) R₀)
          (fullBubbleScaledTail τ cTail (Real.log a)) y*toL2 g.leviCivitaData univ (T z).val y))*
          toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)
    (JSm:H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ)
    (hJSm:∀z:H1Zero g.leviCivitaData univ,JSm z=z+nativeRemoteReturnResponseCLM W (T (JSm z)))
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hfit:a*Real.exp (((m+n:ℕ):ℝ)/2+1)≤R₀)
    (hfitTail:a*(Real.exp cTail+1)≤R₀) (hcTail:Real.log 128≤cTail)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (hfar:NativeH4BaselineFarRealization g gE e (closedBall (0:E) R₀) P ht a S cTail m n χout hχout Rbase)
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (O:Set E) (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero nativeWeakEuclideanD O)
    (hQ₀:∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
      (isCompact_closedBall (0:E) R₀) hsource
      (euclideanL2DilationCLM ha ha1 (toL2 nativeWeakEuclideanD O (L₀ f))))
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (hModel:NativeOriginalModelEnergyRealization hκ0 hκ1 p hp ht χout S O T₀ L₀)
    (f:HalfEndPhysicalH2SourceGraph) (F:E→ℝ) (qi wo:ℝ×SpherePolar.S→ℝ)
    (hL₀:(toL2 nativeWeakEuclideanD O (L₀ f):E→ℝ)=ᵐ[volume]
      fun y=>χout (Real.exp S • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y)
    (hwo:∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T₀ f) s) s wo)
 :
    let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let Z₀:=nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f
    let Z:=JSm Z₀
    let Y₁:=nativeOriginalAffineFeedbackCLM W
      (0:(nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) →L[ℝ] nativeSupportedSourcePairSpace b)
      (ContinuousLinearMap.id ℝ _) (T Z)
    let V:M→ℝ:=fun y=>g.leviCivitaData.scalarCurvature y-8*nativeScaledSmoothBubblePotential e τ a χSm y
    let hV:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V:=g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul hSm)
    ∃C₀ C₁:Lp ℝ 2 g.volumeMeasure,
      (C₀:M→ℝ)=ᵐ[g.volumeMeasure]nativeFiniteCompensationSourceFunction gE e (closedBall (0:E) R₀) a S χout hχout (m+n)
        (fun i=>nativeH4OuterComputedCompensationRow P ht b i (T₀ f)+nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₀.val) ∧
      (C₁:M→ℝ)=ᵐ[g.volumeMeasure]nativeFiniteCompensationSourceFunction gE e (closedBall (0:E) R₀) a S χout hχout (m+n)
        (fun i=>nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₁.val) ∧
      ∃Ft:Lp ℝ 2 g.volumeMeasure,
        (Ft:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>(C₀+C₁:Lp ℝ 2 g.volumeMeasure) y+
          8*nativeScaledSmoothBubblePotential e τ a χSm y*toL2 g.leviCivitaData univ Z y) ∧
        (Z,Ft)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' closedBall (0:E) a)ᶜ ∧
        (Z,C₀+C₁)∈NativeWeakEllipticDataSpace g (e '' closedBall (0:E) a)ᶜ V hV ∧
        ∃u:E→ℝ,Measurable u ∧
          MemLp (fun x=>nativeHalfEndPotentialCoefficient p.potential x*u x) 2
            (volume.restrict (ball (0:E) 1\{0})) ∧
          MemWkpLocally 4 u (ball (0:E) 1\{0}) ∧
          (toL2 g.leviCivitaData univ Z:M→ℝ)=ᵐ[g.volumeMeasure.restrict
            (e '' euclideanDilatedDomain a (ball (0:E) 1))]
              coordinateExtension e (fun x:E=>u (a⁻¹ • x)) ∧
          ∃F_E:Lp ℝ 2 (volume:Measure E),
            (F_E:E→ℝ)=ᵐ[volume](euclideanDilatedDomain a (ball (0:E) 1)).indicator
              (fun x=>gE.pullbackVolumeDensity id x*nativeScaledEffectiveSource gE a
                (halfEndPhysicalH2SourceGraphValue f) p.potential u x) ∧
            let Fi:=nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hsource F_E
            (Z,Fi)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const
              (e '' euclideanDilatedDomain a (ball (0:E) 1)) ∧
            ∃Fg:Lp ℝ 2 g.volumeMeasure,
              (Fg:M→ℝ)=ᵐ[g.volumeMeasure](e '' ball (0:E) a).piecewise (Fi:M→ℝ) (Ft:M→ℝ) ∧
              (Z,Fg)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const univ ∧
              ∀η:H1Zero g.leviCivitaData univ,
                nativeWeakEnergySourceDataCLM g (e '' closedBall (0:E) a)ᶜ
                  (nativeJacobianPotential g (fun _:M=>0)) (nativeJacobianPotential_smooth g contMDiff_const) (Z,Fg) η+
                nativeWeakEnergySourceDataCLM g (e '' closedBall (0:E) a)
                  (nativeJacobianPotential g (fun _:M=>0)) (nativeJacobianPotential_smooth g contMDiff_const) (Z,Fg) η=0 :=by
  dsimp only
  let Z:=JSm (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f)
  obtain ⟨C₀,C₁,hC₀,hC₁,Ft,hFt,hOuter,hData⟩:=exists_nativeSmoothOriginal_same_exterior_solution W hY χSm hSm q hq T hTw JSm hJSm
    hcoeff hfit hfitTail hcTail Rbase hfar T₀ Q₀ O L₀ hQ₀ f F qi wo hL₀ hwo
  obtain ⟨u,hum,hpot,hrep,hu,heq,F_E,hFE,hInner,hInnerData⟩:=
    exists_nativeSmoothOriginal_same_inner_solution hκ0 hκ1 p hp W hcoeff hB hρ T₀ O L₀ Q₀ Rbase hModel hQ₀ T JSm hJSm f
  have hCollar:=nativeSmoothOriginal_same_collar_realization hκ0 hκ1 p hp W hcoeff T₀ O L₀ Q₀ Rbase hModel hQ₀ T JSm hJSm f
  have hReg:=nativeOriginalSource_interior_H4 gE a p.orbit p.smooth p.phase f hu
    (fun U hU hUc hUO=>(heq U hU hUc hUO).2)
  let Fi:=nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hsource F_E
  have hSmall:a≤R₀:=by linarith [W.receiving_fit]
  have hs:closedBall (0:E) a⊆e.source:=(closedBall_subset_closedBall hSmall).trans hsource
  obtain ⟨Fg,hFg,hGlobal⟩:=nativeChartSphere_actual_global_source g e he hei ha hs
    ((nativeActualFeedback_collar_fit W).trans hsource) Z Fi Ft hInner hOuter hCollar.2.2.2.2.2
  have hΩ:MeasurableSet (e '' closedBall (0:E) a)ᶜ:=
    ((isCompact_closedBall (0:E) a).image_of_continuousOn (e.continuousOn.mono hs)).measurableSet.compl
  refine ⟨C₀,C₁,hC₀,hC₁,Ft,hFt,hOuter,hData,u,hum,hpot,hReg,hrep,F_E,hFE,hInner,Fg,hFg,hGlobal,?_⟩
  simpa only [compl_compl] using nativeForcedGlobal_actual_conormal_balance g (e '' closedBall (0:E) a)ᶜ hΩ Z Fg hGlobal

#print axioms exists_nativeSmoothOriginal_same_global_solution
end Yamabe3.Analysis.SpherePolar
