import Yamabe3.Analysis.NativeCollarClassicalGreen

/-! The no-boundary Green identity on the full collar for local C2
fields and compactly supported tests. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.GreenParametrix
open Yamabe3.Analysis.UniformElliptic Yamabe3.Analysis.EuclideanSphereTrace
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

 theorem native_global_classical_green (g : RiemannianMetric 3 E)
    {u ψ : E → ℝ} (hu : ContDiff ℝ 2 u) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : E,nativeCollarClassicalGreenIntegrand g u ψ x)=0 := by
  let ρ := g.pullbackVolumeDensity id
  let L := fun x => ψ x*g.leviCivitaData.laplacian u x*ρ x
  let G := fun x => ∑ i : Fin 3,partialDeriv i ψ x*matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i x
  have hL : Integrable L :=
    ((hψ.continuous.mul (continuous_native_laplacian_C2 g hu)).mul
      (native_density_smooth_positive g).1.continuous).integrable_of_hasCompactSupport hc.mul_right.mul_right
  have hG : Integrable G := by
    apply integrable_finsetSum
    intro i _
    have hflux : Continuous (matrixFlux (nativeDivergenceMatrix g) (fun j => partialDeriv j u) i) :=
      continuous_finsetSum _ (fun j _ => (contDiff_nativeDivergenceMatrix g i j).continuous.mul
        ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const))
    exact (((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hflux).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_right
  have hh := integral_native_mul_laplacian_density_C2 g hψ hu hc
  simp_rw [native_density_gradient_pairing] at hh
  have he : nativeCollarClassicalGreenIntegrand g u ψ = L+G := by
    funext x
    simp only [nativeCollarClassicalGreenIntegrand,Pi.add_apply,L,G,ρ,
      native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData hu.contDiffAt]
    ring
  rw [he]
  change (∫ x : E,L x+G x)=0
  rw [integral_add hL hG]
  change (∫ x : E,L x)=-(∫ x : E,G x) at hh
  rw [hh,neg_add_cancel]

 theorem native_collar_total_classical_green (g : RiemannianMetric 3 E)
    (u : nativeC2OffZero) (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆nativePoissonEntranceCollar) :
    (∫ x in nativePoissonEntranceCollar,nativeCollarClassicalGreenIntegrand g u.val ψ x)=0 := by
  obtain ⟨F,hF,-,hg⟩ := exists_compact_C2_extension_near_compact isClosed_singleton.isOpen_compl
    (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2)) u.property
  calc
    _ = ∫ x in nativePoissonEntranceCollar,nativeCollarClassicalGreenIntegrand g F ψ x := by
      apply setIntegral_congr_fun (nativePolarTimeWindow_open (1/2)).measurableSet
      intro x hx
      have hxg := hg x (subset_closure hx)
      have hp (j : Fin 3) : partialDeriv j F x=partialDeriv j u.val x :=
        congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) hxg.fderiv_eq
      simp only [nativeCollarClassicalGreenIntegrand,principalSource_eq_of_eventuallyEq _ hxg,matrixFlux,hp]
    _ = ∫ x : E,nativeCollarClassicalGreenIntegrand g F ψ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hn : x∉tsupport ψ := fun h => hx (hs h)
      have hp (i : Fin 3) : partialDeriv i ψ x=0 := by
        unfold partialDeriv
        rw [fderiv_of_notMem_tsupport ℝ hn]
        rfl
      simp only [nativeCollarClassicalGreenIntegrand,image_eq_zero_of_notMem_tsupport hn,hp,zero_mul,
        Finset.sum_const_zero,add_zero]
    _ = 0 := native_global_classical_green g hF hψ hc

#print axioms native_global_classical_green
#print axioms native_collar_total_classical_green
end Yamabe3.Analysis.SpherePolar
