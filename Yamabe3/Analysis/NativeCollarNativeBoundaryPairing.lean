import Yamabe3.Analysis.NativeCollarJetTrace
import Yamabe3.Analysis.NativeGaussSphereBoundaryFlux

/-! Pairing of the constructed radial trace with the actual induced
native sphere measure. This fixes measure and orientation; the Green
identity still has to identify it as the weak conormal. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open GreenMass.NativeGaussSphereArea Yamabe3.Analysis.GreenParametrix

theorem native_unit_sphere_integral_density (g : RiemannianMetric 3 E)
    (hGauss : ∀ (θ : S) (v : E),g.inner (θ:E) (θ:E) v=inner ℝ (θ:E) v)
    (f : S → ℝ) :
    (∫ θ : S,f θ ∂(gaussRadiusMetric g 1 (by norm_num)).volumeMeasure)=
      ∫ θ : S,g.pullbackVolumeDensity id (θ:E)*f θ ∂angularVolume := by
  have hg : ∀ (θ : S) (v : E),g.inner ((1:ℝ) • (θ:E)) ((1:ℝ) • (θ:E)) v=
      inner ℝ ((1:ℝ) • (θ:E)) v := by
    intro θ v
    change (g.euclideanCoefficients ((1:ℝ) • (θ:E))) ((1:ℝ) • (θ:E)) v=_
    simp only [one_smul]
    exact hGauss θ v
  rw [gaussRadiusMetric_volume_eq_weighted_polarArea g 1 (by norm_num) hg]
  simp only [one_pow,ENNReal.ofReal_one,one_smul,GreenMass.SphereMeasure.dilation,polar_sphereMeasure_eq_native]
  have hρ := native_density_smooth_positive g
  have hm : Measurable (fun θ : S => ENNReal.ofReal (g.pullbackVolumeDensity id (θ:E))) :=
    ENNReal.continuous_ofReal.measurable.comp (hρ.1.continuous.comp continuous_subtype_val).measurable
  change (∫ θ : S,f θ ∂angularVolume.withDensity (fun θ => ENNReal.ofReal (g.pullbackVolumeDensity id (θ:E))))=_
  rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    change (ENNReal.ofReal (g.pullbackVolumeDensity id (θ:E))).toReal • f θ=_
    rw [ENNReal.toReal_ofReal (hρ.2 _).le,smul_eq_mul]

def nativeSphereWeightedTest (g : RiemannianMetric 3 E) (ψ : E → ℝ) (hψ : Continuous ψ) :
    Lp ℝ 2 angularVolume :=
  (native_continuous_sphere_memLp (((native_density_smooth_positive g).1.continuous.mul hψ).comp
    continuous_subtype_val)).toLp (fun θ : S => g.pullbackVolumeDensity id (θ:E)*ψ (θ:E))

theorem nativeSphereWeightedTest_ae (g : RiemannianMetric 3 E) (ψ : E → ℝ) (hψ : Continuous ψ) :
    (nativeSphereWeightedTest g ψ hψ : S → ℝ)=ᵐ[angularVolume]
      (fun θ => g.pullbackVolumeDensity id (θ:E)*ψ (θ:E)) := MemLp.coeFn_toLp _

def nativeCollarNativeNormalPairCLM (g : RiemannianMetric 3 E) (ψ : E → ℝ) (hψ : Continuous ψ) :
    nativeCollarJetClosure →L[ℝ] ℝ :=
  (innerSL ℝ (nativeSphereWeightedTest g ψ hψ)).comp nativeCollarNormalTraceCLM

theorem nativeCollarNativeNormalPair_eq_integral (g : RiemannianMetric 3 E)
    (hGauss : ∀ (θ : S) (v : E),g.inner (θ:E) (θ:E) v=inner ℝ (θ:E) v)
    (ψ : E → ℝ) (hψ : Continuous ψ) (J : nativeCollarJetClosure) :
    nativeCollarNativeNormalPairCLM g ψ hψ J=
      ∫ θ : S,ψ (θ:E)*(nativeCollarNormalTraceCLM J : S → ℝ) θ
        ∂(gaussRadiusMetric g 1 (by norm_num)).volumeMeasure := by
  change inner ℝ (nativeSphereWeightedTest g ψ hψ) (nativeCollarNormalTraceCLM J)=_
  rw [L2.inner_def,native_unit_sphere_integral_density g hGauss]
  apply integral_congr_ae
  filter_upwards [nativeSphereWeightedTest_ae g ψ hψ] with θ hθ
  simp only [RCLike.inner_apply,conj_trivial,hθ]
  ring

#print axioms native_unit_sphere_integral_density
#print axioms nativeCollarNativeNormalPair_eq_integral
end Yamabe3.Analysis.SpherePolar
