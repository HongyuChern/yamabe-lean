import Yamabe3.Analysis.NativeSphereDensityGreenC2
import Yamabe3.Analysis.NativeLocalC2CauchyGluing

/-! Local C2 Green identity for tests supported in the actual entrance
collar. The test can cross the sphere and have nonzero boundary value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Yamabe3.Analysis.EuclideanSphereTrace
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

def nativeCollarClassicalGreenIntegrand (g : RiemannianMetric 3 E) (u ψ : E → ℝ) (x : E) : ℝ :=
  ψ x*(-principalSource (nativeDivergenceMatrix g) u x)+
    ∑ i : Fin 3,partialDeriv i ψ x*matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i x

theorem native_unit_sphere_mem_collar (θ : S) : (θ:E)∈nativePoissonEntranceCollar := by
  apply (nativePolarTimeWindow_norm (1/2) (θ:E)).mpr
  rw [norm_eq_of_mem_sphere θ]
  exact ⟨Real.exp_lt_one_iff.mpr (by norm_num),Real.one_lt_exp_iff.mpr (by norm_num)⟩

private theorem integrand_zero_off_collar (g : RiemannianMetric 3 E) (u ψ : E → ℝ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) {x : E} (hx : x∉nativePoissonEntranceCollar) :
    nativeCollarClassicalGreenIntegrand g u ψ x=0 := by
  have hn : x∉tsupport ψ := fun h => hx (hs h)
  have hp : ∀ i : Fin 3,partialDeriv i ψ x=0 := by
    intro i
    unfold partialDeriv
    rw [fderiv_of_notMem_tsupport ℝ hn]
    rfl
  simp only [nativeCollarClassicalGreenIntegrand,image_eq_zero_of_notMem_tsupport hn,hp,zero_mul,
    Finset.sum_const_zero,add_zero]

private theorem integrand_germ (g : RiemannianMetric 3 E) (ψ : E → ℝ)
    {F u : E → ℝ} {x : E} (h : F=ᶠ[𝓝 x]u) :
    nativeCollarClassicalGreenIntegrand g F ψ x=nativeCollarClassicalGreenIntegrand g u ψ x := by
  have hp (j : Fin 3) : partialDeriv j F x=partialDeriv j u x := congrArg
    (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) h.fderiv_eq
  simp only [nativeCollarClassicalGreenIntegrand,principalSource_eq_of_eventuallyEq _ h,matrixFlux,hp]

 theorem native_collar_classical_green (g : RiemannianMetric 3 E)
    (hGauss : ∀ x v : E,g.inner x x v=inner ℝ x v)
    (u : nativeC2OffZero) (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) :
    (∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},nativeCollarClassicalGreenIntegrand g u.val ψ x)=
      -(∫ θ : S,g.pullbackVolumeDensity id (θ:E)*(ψ (θ:E)*fderiv ℝ u.val (θ:E) (θ:E)) ∂angularVolume) := by
  obtain ⟨F,hF,-,hg⟩ := exists_compact_C2_extension_near_compact isClosed_singleton.isOpen_compl
    (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2)) u.property
  have hglobal := native_exterior_density_green_C2 g hGauss hF hψ hc
  have hlocal : (∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},nativeCollarClassicalGreenIntegrand g F ψ x)=
      ∫ x in {y : E | 1<‖y‖},nativeCollarClassicalGreenIntegrand g F ψ x := by
    have hΩ : MeasurableSet nativePoissonEntranceCollar := (nativePolarTimeWindow_open (1/2)).measurableSet
    rw [← Measure.restrict_restrict hΩ]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => integrand_zero_off_collar g F ψ hs hx)
  have hsame : (∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},nativeCollarClassicalGreenIntegrand g u.val ψ x)=
      ∫ x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},nativeCollarClassicalGreenIntegrand g F ψ x := by
    apply setIntegral_congr_fun ((nativePolarTimeWindow_open (1/2)).measurableSet.inter
      (isOpen_lt continuous_const continuous_norm).measurableSet)
    intro x hx
    exact (integrand_germ g ψ (hg x (subset_closure hx.1))).symm
  rw [hsame,hlocal]
  change (∫ x in {y : E | 1<‖y‖},ψ x*(-principalSource (nativeDivergenceMatrix g) F x)+
    ∑ i : Fin 3,partialDeriv i ψ x*matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j F) i x)=_
  rw [hglobal]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    dsimp only
    have hd : fderiv ℝ F (θ:E)=fderiv ℝ u.val (θ:E) :=
      (hg (θ:E) (subset_closure (native_unit_sphere_mem_collar θ))).fderiv_eq
    rw [hd]

#print axioms native_unit_sphere_mem_collar
#print axioms native_collar_classical_green
end Yamabe3.Analysis.SpherePolar
