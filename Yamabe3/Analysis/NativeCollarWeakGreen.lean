import Yamabe3.Analysis.NativeCollarGreenVolume

/-! Native Green formula on the actual strong C2 H2-jet closure. The
formula is proved by density and continuity of its real volume and
boundary pairings, rather than supplied as a conormal assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open GreenMass.NativeGaussSphereArea

private theorem normal_pair_C2 (g : RiemannianMetric 3 E) (ψ : E → ℝ) (hψ : Continuous ψ)
    (u : nativeC2OffZero) :
    nativeCollarNativeNormalPairCLM g ψ hψ (nativeC2CollarJetInclusion u)=
      ∫ θ : S,g.pullbackVolumeDensity id (θ:E)*(ψ (θ:E)*fderiv ℝ u.val (θ:E) (θ:E)) ∂angularVolume := by
  change inner ℝ (nativeSphereWeightedTest g ψ hψ) (nativeCollarNormalTraceCLM (nativeC2CollarJetInclusion u))=_
  rw [(nativeCollarTraceCLM_agrees_C2 u).2,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [nativeSphereWeightedTest_ae g ψ hψ,
    (native_C1_sphere_normal_memLp (u.property.of_le (by norm_num))).coeFn_toLp] with θ hφ hu
  have hux : (nativeC2NormalTraceLinear u : S → ℝ) θ=fderiv ℝ u.val (θ:E) (θ:E) := hu
  simp only [RCLike.inner_apply,conj_trivial,hφ,hux]
  ring

 theorem nativeCollarWeakGreen (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E,g.inner x x v=inner ℝ x v)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) (J : nativeCollarJetClosure) :
    nativeCollarGreenVolumeCLM g ψ hψ J.val = -nativeCollarNativeNormalPairCLM g ψ hψ.continuous J := by
  have he : (fun J : nativeCollarJetClosure => nativeCollarGreenVolumeCLM g ψ hψ J.val)=
      (fun J : nativeCollarJetClosure => -nativeCollarNativeNormalPairCLM g ψ hψ.continuous J) := by
    apply nativeC2CollarJetInclusion_dense.equalizer
      ((nativeCollarGreenVolumeCLM g ψ hψ).continuous.comp continuous_subtype_val)
      (nativeCollarNativeNormalPairCLM g ψ hψ.continuous).continuous.neg
    funext u
    change nativeCollarGreenVolumeCLM g ψ hψ (nativeC2CollarJetLinear u)=
      -nativeCollarNativeNormalPairCLM g ψ hψ.continuous (nativeC2CollarJetInclusion u)
    rw [nativeCollarGreenVolume_C2,native_collar_classical_green g hGauss u ψ hψ hc hs,
      normal_pair_C2]
  exact congrFun he J

 theorem nativeCollarWeakGreen_integral (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E,g.inner x x v=inner ℝ x v)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) (J : nativeCollarJetClosure) :
    (∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},
      ψ x*(nativeCollarDensityLaplacianCLM g J.val : E → ℝ) x+
        ∑ j : Fin 3,nativeCollarGradientTest g ψ j x*(J.val.2.1 j : E → ℝ) x)=
      -(∫ θ : S,ψ (θ:E)*(nativeCollarNormalTraceCLM J : S → ℝ) θ
        ∂(gaussRadiusMetric g 1 (by norm_num)).volumeMeasure) := by
  rw [← nativeCollarGreenVolume_eq_integral g ψ hψ J.val,nativeCollarWeakGreen g hGauss ψ hψ hc hs J,
    nativeCollarNativeNormalPair_eq_integral g (fun θ v => hGauss θ v)]

 theorem nativeCollarWeakGreen_exterior_eight (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E,g.inner x x v=inner ℝ x v)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) (J : nativeCollarJetClosure) :
    8*nativeCollarGreenVolumeCLM g ψ hψ J.val=
      -8*(∫ θ : S,ψ (θ:E)*(nativeCollarNormalTraceCLM J : S → ℝ) θ
        ∂(gaussRadiusMetric g 1 (by norm_num)).volumeMeasure) := by
  rw [nativeCollarWeakGreen g hGauss ψ hψ hc hs J,
    nativeCollarNativeNormalPair_eq_integral g (fun θ v => hGauss θ v)]
  ring

#print axioms nativeCollarWeakGreen
#print axioms nativeCollarWeakGreen_integral
#print axioms nativeCollarWeakGreen_exterior_eight
end Yamabe3.Analysis.SpherePolar
