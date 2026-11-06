import Yamabe3.Analysis.NativeOriginalAffineInnerEquation
import Yamabe3.Analysis.NativeOriginalModelFlatSource
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


theorem nativeOriginalAffine_inner_original_source
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (f:HalfEndPhysicalH2SourceGraph) (x:HalfEndPhysicalH4Graph) (F u:E→ℝ)
    (hF:EqOn (nativeH4GraphFunction x) F (closedBall (0:E) 4))
    (hmodel:F=ᵐ[volume.restrict (ball (0:E) 1\{0})]fullModelPhysicalField hκ0 hκ1 p f)
    (hu:∀i:HalfEndPhysicalSliceIndex,
      ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x+
        nativeTwoSidedAllScaleJetCLM P hp v hv hb τ i.val
          (nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase x).val).val.1:E→ℝ)
        =ᵐ[volume.restrict nativePoissonEntranceCollar]
          fun y=>Real.exp (3*i.val/2)*u (Real.exp (-i.val) • y)) :
    MemWkpLocally 2 u (ball (0:E) 1\{0}) ∧
      ∀U:Set E,IsOpen U → IsCompact (closure U) → closure U⊆ball (0:E) 1\{0} →
        MemWkp 2 2 u U ∧ nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u
          =ᵐ[volume.restrict U]fun y=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) y/8 := by
  have hh:=nativeOriginalAffine_inner_local_equation hκ0 hκ1 p hp W hB hρ Rbase x F u hF hu
  refine ⟨hh.1,fun U hU hUc hUO=>?_⟩
  obtain ⟨huU,he⟩:=hh.2 U hU hUc hUO
  exact ⟨huU,he.trans (nativeOriginalModel_flat_same_source hκ0 hκ1 p f F hmodel hU hUc hUO).2⟩

#print axioms nativeOriginalAffine_inner_original_source
end Yamabe3.Analysis.SpherePolar
