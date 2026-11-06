import Yamabe3.Analysis.NativePhysicalConormalMatching
import Yamabe3.Analysis.NativeActualFeedbackBoundaryGeometry
import Yamabe3.Analysis.NativeSmoothOriginalGlobalRealization
import Yamabe3.Analysis.NativeSmoothOriginalGlobalAssembly
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



theorem exists_nativeOriginal_actual_physical_closure
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hGauss:∀x z:E,gE.inner x x z=inner ℝ x z)
    {Cρ:ℝ} (hCρ:0≤Cρ) (hρ:∀θ:SpherePolar.S,gE.pullbackVolumeDensity id (a • (θ:E))≤Cρ)
    (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
    (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (χSm:E→ℝ) (hSm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ (nativeScaledSmoothBubblePotential e τ a χSm))
    (T:(H1Zero g.leviCivitaData univ) →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (JSm:H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ)
    (hReal:NativeSmoothOriginalGlobalRealization hκ0 hκ1 p hp W T₀ Q₀ Rbase χSm hSm T JSm)
    (f:HalfEndPhysicalH2SourceGraph):
    let Z:=JSm (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f)
    let Y₀:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase (T₀ f)
    let Y₁:=nativeOriginalAffineFeedbackCLM W
      (0:(nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))) →L[ℝ] nativeSupportedSourcePairSpace b)
      (ContinuousLinearMap.id ℝ _) (T Z)
    ∃C₀ C₁ Fg:Lp ℝ 2 g.volumeMeasure,
      (C₀:M→ℝ)=ᵐ[g.volumeMeasure]nativeFiniteCompensationSourceFunction gE e (closedBall (0:E) R₀) a S χout hχout (m+n)
        (fun i=>nativeH4OuterComputedCompensationRow P ht b i (T₀ f)+nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₀.val) ∧
      (C₁:M→ℝ)=ᵐ[g.volumeMeasure]nativeFiniteCompensationSourceFunction gE e (closedBall (0:E) R₀) a S χout hχout (m+n)
        (fun i=>nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₁.val) ∧
      ∃hData:(Z,C₀+C₁)∈NativeWeakEllipticDataSpace g (e '' closedBall (0:E) a)ᶜ
        (fun y=>g.leviCivitaData.scalarCurvature y-8*nativeScaledSmoothBubblePotential e τ a χSm y)
        (g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul hSm)),
        (Z,Fg)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const univ ∧
        NativePhysicalConormalMatching g gE e he hei hGauss ha
          (nativeActualFeedback_double_ball_source W) (nativeActualFeedback_boundary_coeff W hcoeff) hCρ hρ
          (nativeScaledSmoothBubblePotential e τ a χSm) hSm Z Fg (C₀+C₁) hData:=by
  dsimp only
  let Z:=JSm (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase f)
  obtain ⟨C₀,C₁,hC₀,hC₁,Ft,hFt,hOuter,hData,u,hum,hpot,hu4,hrep,F_E,hFE,hInner,Fg,hFg,hGlobal,hBalance⟩:=hReal f
  have hΩ:MeasurableSet (e '' closedBall (0:E) a)ᶜ:=
    ((isCompact_closedBall (0:E) a).image_of_continuousOn
      (e.continuousOn.mono ((closedBall_subset_closedBall (by linarith only [ha])).trans
        (nativeActualFeedback_double_ball_source W)))).measurableSet.compl
  have hSrc:(Fg:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' closedBall (0:E) a)ᶜ]
      (fun y=>(C₀+C₁:Lp ℝ 2 g.volumeMeasure) y+8*nativeScaledSmoothBubblePotential e τ a χSm y*
        toL2 g.leviCivitaData univ Z y):=by
    filter_upwards [ae_restrict_of_ae (s:=(e '' closedBall (0:E) a)ᶜ) hFg,
      ae_restrict_of_ae (s:=(e '' closedBall (0:E) a)ᶜ) hFt,ae_restrict_mem hΩ] with y hyF hyT hyΩ
    have hn:y∉e '' ball (0:E) a:=fun hyB=>hyΩ (image_mono ball_subset_closedBall hyB)
    exact (hyF.trans (piecewise_eq_of_notMem _ _ _ hn)).trans hyT
  exact ⟨C₀,C₁,Fg,hC₀,hC₁,hData,hGlobal,
    nativeSmoothGlobal_physical_conormal_dual_balance g gE e he hei hGauss ha
      (nativeActualFeedback_double_ball_source W) (nativeActualFeedback_boundary_coeff W hcoeff) hCρ hρ
      (nativeScaledSmoothBubblePotential e τ a χSm) hSm Z Fg (C₀+C₁) hGlobal hSrc hData⟩

#print axioms exists_nativeOriginal_actual_physical_closure
end Yamabe3.Analysis.SpherePolar
