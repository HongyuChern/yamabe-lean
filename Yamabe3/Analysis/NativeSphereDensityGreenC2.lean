import Yamabe3.Analysis.NativeSphereGreenC2
import Yamabe3.Analysis.NativeCollarNativeBoundaryPairing

/-! The genuine native Green formula in coefficient/volume form. The
same native density appears in both the divergence and induced area. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Yamabe3.Analysis.EuclideanSphereTrace
open Yamabe3.Analysis.GreenParametrix
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

 theorem native_setIntegral_eq_density (g : RiemannianMetric 3 E) {T : Set E}
    (hT : MeasurableSet T) (f : E → ℝ) :
    (∫ x in T,f x ∂g.volumeMeasure)=∫ x in T,f x*g.pullbackVolumeDensity id x := by
  rw [← integral_indicator hT,native_integral_eq_density g,← integral_indicator hT]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x∈T
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,zero_mul]

 theorem native_density_gradient_pairing (g : RiemannianMetric 3 E) (u ψ : E → ℝ) (x : E) :
    g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient u x)*g.pullbackVolumeDensity id x=
      ∑ i : Fin 3,partialDeriv i ψ x*matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i x := by
  rw [g.leviCivitaData.inner_gradient]
  simp +instances only [mvfderiv,mfderiv_eq_fderiv,NormedSpace.fromTangentSpace]
  change fderiv ℝ ψ x (g.leviCivitaData.gradient u x)*g.pullbackVolumeDensity id x=_
  have he (L : E →L[ℝ] ℝ) (v : E) : L v=∑ i : Fin 3,L (EuclideanSpace.single i 1)*v i := by
    have h := congrArg L ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.sum_repr v)
    simpa only [map_sum,map_smul,smul_eq_mul,OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,mul_comm] using h.symm
  rw [he,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [matrixFlux_native_eq_density_gradient g g.leviCivitaData]
  change (partialDeriv i ψ x*WithLp.ofLp (show E from g.leviCivitaData.gradient u x) i)*g.pullbackVolumeDensity id x=_
  ring

 theorem native_exterior_density_green_C2 (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E,g.inner x x v=inner ℝ x v)
    {u ψ : E → ℝ} (hu : ContDiff ℝ 2 u) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∫ x in {y : E | 1<‖y‖},ψ x*(-principalSource (nativeDivergenceMatrix g) u x)+
      ∑ i : Fin 3,partialDeriv i ψ x*matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i x)=
      -(∫ θ : S,g.pullbackVolumeDensity id (θ:E)*(ψ (θ:E)*fderiv ℝ u (θ:E) (θ:E)) ∂angularVolume) := by
  have h := integral_native_exterior_sphere_green_C2 g hGauss (by norm_num : (0:ℝ)<1) hu hψ hc
  have hT : MeasurableSet {y : E | 1<‖y‖} := isOpen_lt continuous_const continuous_norm |>.measurableSet
  rw [native_setIntegral_eq_density g hT,native_unit_sphere_integral_density g (fun θ v => hGauss θ v)] at h
  simp only [one_smul] at h
  convert h using 1
  apply setIntegral_congr_fun hT
  intro x _
  dsimp only
  rw [add_mul,native_density_gradient_pairing,
    native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData hu.contDiffAt]
  ring

#print axioms native_setIntegral_eq_density
#print axioms native_density_gradient_pairing
#print axioms native_exterior_density_green_C2
end Yamabe3.Analysis.SpherePolar
