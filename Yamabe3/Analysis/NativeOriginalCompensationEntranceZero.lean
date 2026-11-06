import Yamabe3.Analysis.NativeFiniteCompensationLocalZero
import Yamabe3.Analysis.NativeCompensationEntranceSupport
import Yamabe3.Analysis.NativeActualFeedbackCollarIdentity
import Yamabe3.Analysis.NativeOriginalWholeExteriorEquation
import Yamabe3.Analysis.NativeSmoothPotentialFixedFieldEquation
import Yamabe3.Analysis.NativeSmoothPotentialFeedback
import Yamabe3.Analysis.NativeOriginalWholeOuterWeakEquation
import Yamabe3.Analysis.NativeOriginalCompensationSource
import Yamabe3.Analysis.NativeWholeExteriorTestAdapter
import Yamabe3.Analysis.NativeWholeFullBubbleCompletedPairing
import Yamabe3.Analysis.NativeFullBubbleSignedPairing
import Yamabe3.Analysis.NativeL2ReactionSource

/-! The SAME original-source SIGNED completed field satisfies its
actual native weak equation on the whole native exterior. A fixed
computed compensation and the same full reaction construct one L2
source BEFORE all tests. This is the hard compact-chart full potential;
no smooth-paper truncation or conormal acceptance is inferred. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
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


include W in
theorem nativeOriginal_computed_sources_zero_entrance
    (x:HalfEndPhysicalH4Graph) (Y₀ Y₁:nativeSupportedSourcePairSpace b) (C₀ C₁:Lp ℝ 2 g.volumeMeasure)
    (hC₀:(C₀:M→ℝ)=ᵐ[g.volumeMeasure]nativeFiniteCompensationSourceFunction gE e (closedBall (0:E) R₀) a S χout hχout (m+n)
      (fun i=>nativeH4OuterComputedCompensationRow P ht b i x+nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₀.val))
    (hC₁:(C₁:M→ℝ)=ᵐ[g.volumeMeasure]nativeFiniteCompensationSourceFunction gE e (closedBall (0:E) R₀) a S χout hχout (m+n)
      (fun i=>nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₁.val)):
    (C₀:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)](fun _=>0) ∧
    (C₁:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)](fun _=>0):=by
  let D:=euclideanDilatedDomain a nativePoissonEntranceCollar
  let f₀:Fin (m+n)→E→ℝ:=fun i=>nativeSupportedLowCompensationScaled b ht 0
    (nativeH4GraphAngularValueCLM x) (nativeH4GraphAngularNormalCLM x) (nativeOuterLogShellCenter i)
  let fY:(nativeSupportedSourcePairSpace b)→Fin (m+n)→E→ℝ:=fun Y i=>
    nativeSupportedLowCompensationScaled b ht Y.val.2 (nativeLowL2AngularCLM v hv hb Y.val.1 0)
      (nativeFullL2NormalAngularCLM P hp v hv hb Y.val.1) (nativeOuterLogShellCenter i)
  have h₀(i:Fin (m+n)):(nativeH4OuterComputedCompensationRow P ht b i x:E→ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar]f₀ i:=
    nativeSupportedLowCauchyAllScale_source b ht 0 (nativeH4GraphAngularValueCLM x)
      (nativeH4GraphAngularNormalCLM x) (nativeOuterLogShellCenter i)
  have hY(Y:nativeSupportedSourcePairSpace b)(i:Fin (m+n)):
      (nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y.val:E→ℝ)
        =ᵐ[volume.restrict nativePoissonEntranceCollar]fY Y i:=
    nativeSupportedLowCauchyAllScale_source b ht Y.val.2 (nativeLowL2AngularCLM v hv hb Y.val.1 0)
      (nativeFullL2NormalAngularCLM P hp v hv hb Y.val.1) (nativeOuterLogShellCenter i)
  have hz₀(i:Fin (m+n))(z:E)(hz:z∈D):f₀ i (Real.exp (nativeOuterLogShellCenter i-Real.log a) • z)=0:=
    nativeSupportedScaledCompensation_zero_entrance b ht 0 (nativeH4GraphAngularValueCLM x)
      (nativeH4GraphAngularNormalCLM x) ha (nativeOuterLogShellCenter i) z hz
  have hzY(Y:nativeSupportedSourcePairSpace b)(i:Fin (m+n))(z:E)(hz:z∈D):
      fY Y i (Real.exp (nativeOuterLogShellCenter i-Real.log a) • z)=0:=
    nativeSupportedScaledCompensation_zero_entrance b ht Y.val.2 (nativeLowL2AngularCLM v hv hb Y.val.1 0)
      (nativeFullL2NormalAngularCLM P hp v hv hb Y.val.1) ha (nativeOuterLogShellCenter i) z hz
  have hSum(i:Fin (m+n)):
      (nativeH4OuterComputedCompensationRow P ht b i x+nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₀.val:NativeCollarL2)
        =ᵐ[volume.restrict nativePoissonEntranceCollar](fun z=>f₀ i z+fY Y₀ i z):=by
    filter_upwards [h₀ i,hY Y₀ i,Lp.coeFn_add (nativeH4OuterComputedCompensationRow P ht b i x)
      (nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₀.val)] with z hz₀ hzy hs
    rw [hs]
    change nativeH4OuterComputedCompensationRow P ht b i x z+
      nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₀.val z=_
    rw [hz₀,hzy]
  have hZero₀:=nativeFiniteCompensationSource_zero_entrance g gE e he hei hsource a S χout hχout (m+n)
    (fun i=>nativeH4OuterComputedCompensationRow P ht b i x+nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₀.val)
    (fun i z=>f₀ i z+fY Y₀ i z) (nativeActualFeedback_collar_fit W) hSum
    (fun i z hz=>by rw [hz₀ i z hz,hzY Y₀ i z hz,add_zero])
  have hZero₁:=nativeFiniteCompensationSource_zero_entrance g gE e he hei hsource a S χout hχout (m+n)
    (fun i=>nativeFiniteWindowOuterCompensationRow P hp v hv hb b ht i Y₁.val) (fY Y₁)
    (nativeActualFeedback_collar_fit W) (hY Y₁) (hzY Y₁)
  exact ⟨Filter.EventuallyEq.trans (ae_restrict_of_ae (s:=e '' D) hC₀) hZero₀,Filter.EventuallyEq.trans (ae_restrict_of_ae (s:=e '' D) hC₁) hZero₁⟩

#print axioms nativeOriginal_computed_sources_zero_entrance
end Yamabe3.Analysis.SpherePolar
