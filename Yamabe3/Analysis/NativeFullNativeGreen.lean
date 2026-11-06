import Yamabe3.Analysis.NativeFullEntranceTraces
import Yamabe3.Analysis.NativeCollarInteriorWeakGreen

/-! The same full-source collar jet carries both genuine boundary traces
and the native Green pairing with its true induced surface measure.
The lower-order Jacobian potential does not alter this normal pairing. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay GreenMass.NativeGaussSphereArea
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1)

theorem nativeFullDelaunay_native_green (p : DelaunayPhaseData κ)
    (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
    (g : RiemannianMetric 3 E) (hGauss : ∀ x v : E,g.inner x x v=inner ℝ x v)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) :
    let J := nativeFullDelaunayJetCLM hκ0 hκ1 p hp 0 F
    nativeCollarGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet g ψ hψ J.val=
      nativeCollarNativeNormalPairCLM g ψ hψ.continuous J ∧
    nativeCollarGreenVolumeCLM g ψ hψ J.val= -nativeCollarNativeNormalPairCLM g ψ hψ.continuous J ∧
    nativeCollarNativeNormalPairCLM g ψ hψ.continuous J=
      ∫ θ : S,ψ (θ:E)*(nativeCollarNormalTraceCLM J : S → ℝ) θ
        ∂(gaussRadiusMetric g 1 (by norm_num)).volumeMeasure :=
  ⟨nativeCollarWeakGreen_interior g hGauss ψ hψ hc hs _,
    nativeCollarWeakGreen g hGauss ψ hψ hc hs _,
    nativeCollarNativeNormalPair_eq_integral g (fun θ z => hGauss (θ:E) z) ψ hψ.continuous _⟩

theorem exists_uniform_nativeFullDelaunay_trace_bound :
    ∃ C : ℝ,0<C ∧ ∀ (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
      (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)),
      ‖nativeCollarValueTraceCLM (nativeFullDelaunayJetCLM hκ0 hκ1 p hp 0 F)‖+
        ‖nativeCollarNormalTraceCLM (nativeFullDelaunayJetCLM hκ0 hκ1 p hp 0 F)‖≤C*‖F‖ := by
  obtain ⟨B,hB,h⟩ := exists_uniform_nativeFullDelaunayJet_bound hκ0 hκ1
  let L := ‖nativeCollarValueTraceCLM‖+‖nativeCollarNormalTraceCLM‖
  have hL : 0≤L := add_nonneg (norm_nonneg nativeCollarValueTraceCLM)
    (norm_nonneg nativeCollarNormalTraceCLM)
  refine ⟨(L+1)*B,by positivity,fun p hp F => ?_⟩
  let J := nativeFullDelaunayJetCLM hκ0 hκ1 p hp 0 F
  have hJ : ‖J‖≤B*‖F‖ := (nativeFullDelaunayRawJetCLM hκ0 hκ1 p hp 0).le_of_opNorm_le (h p hp 0) F
  have hh := add_le_add (nativeCollarValueTraceCLM.le_opNorm J) (nativeCollarNormalTraceCLM.le_opNorm J)
  calc
    _≤L*‖J‖ := hh.trans_eq (by dsimp only [L];ring)
    _≤L*(B*‖F‖) := mul_le_mul_of_nonneg_left hJ hL
    _≤((L+1)*B)*‖F‖ := by nlinarith [mul_nonneg hB.le (norm_nonneg F)]

#print axioms nativeFullDelaunay_native_green
#print axioms exists_uniform_nativeFullDelaunay_trace_bound
end Yamabe3.Analysis.SpherePolar
