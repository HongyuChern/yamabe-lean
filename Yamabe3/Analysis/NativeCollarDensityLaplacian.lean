import Yamabe3.Analysis.NativeCollarJetWeakDerivatives
import Yamabe3.Analysis.NativeDivergenceC2
import Yamabe3.Analysis.NativeC2GeometricError

/-! The same collar jet gives the actual density-weighted native Laplacian,
through the genuine divergence matrix and its first derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

def nativeCollarDivergenceFirst (g : RiemannianMetric 3 E) (j : Fin 3) (x : E) : ℝ :=
  ∑ i : Fin 3,partialDeriv i (fun y => nativeDivergenceMatrix g y i j) x

theorem continuous_nativeCollarDivergenceFirst (g : RiemannianMetric 3 E) (j : Fin 3) :
    Continuous (nativeCollarDivergenceFirst g j) :=
  (ContDiff.sum (fun i _ => contDiff_partial (contDiff_nativeDivergenceMatrix g i j) i)).continuous

def nativeCollarDensityLaplacianCLM (g : RiemannianMetric 3 E) : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  nativeCollarJetPerturbationCLM (fun i j x => nativeDivergenceMatrix g x i j)
    (nativeCollarDivergenceFirst g) (fun _ => 0)
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).continuous)
    (continuous_nativeCollarDivergenceFirst g) continuous_const

theorem nativeCollarDensityLaplacian_C2_ae (g : RiemannianMetric 3 E) (u : nativeC2OffZero) :
    (nativeCollarDensityLaplacianCLM g (nativeC2CollarJetLinear u) : E → ℝ)
      =ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x) := by
  have hm := nativeC2Collar_memLp u.property
  have h := nativeCollarJetPerturbationCLM_ae (fun i j x => nativeDivergenceMatrix g x i j)
    (nativeCollarDivergenceFirst g) (fun _ => 0)
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).continuous)
    (continuous_nativeCollarDivergenceFirst g) continuous_const (nativeC2CollarJetLinear u)
  filter_upwards [h,eventually_all.mpr (fun i => eventually_all.mpr (fun j => (hm.2.2 i j).coeFn_toLp)),
    eventually_all.mpr (fun j => (hm.2.1 j).coeFn_toLp),
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx h2 h1 hxO
  have hux : ContDiffAt ℝ 2 u.val x := u.property.contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds
      (subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2)) hxO))
  have hd := native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData hux
  have hp := principalSource_eq_secondOrderOperator_C2_at (nativeCollarDivergenceFirst g)
    (contDiff_nativeDivergenceMatrix g) x hux
  simp only [nativeCollarDivergenceFirst,sub_self,zero_mul,Finset.sum_const_zero,add_zero] at hp
  change nativeCollarDensityLaplacianCLM g (nativeC2CollarJetLinear u) x=_
  unfold nativeCollarDensityLaplacianCLM
  rw [hx]
  change (∑ i : Fin 3,∑ j : Fin 3,nativeDivergenceMatrix g x i j*(nativeC2CollarSecond u.property i j : E → ℝ) x)+
    (∑ j : Fin 3,nativeCollarDivergenceFirst g j x*(nativeC2CollarFirst u.property j : E → ℝ) x)+0*(nativeC2CollarValue u.property : E → ℝ) x=_
  have hh2 (i j : Fin 3) : (nativeC2CollarSecond u.property i j : E → ℝ) x=nativeCoordinateSecond i j u.val x := h2 i j
  have hh1 (j : Fin 3) : (nativeC2CollarFirst u.property j : E → ℝ) x=nativeCoordinateFirst j u.val x := h1 j
  simp only [hh2,hh1,zero_mul,add_zero]
  change secondOrderOperator (nativeDivergenceMatrix g) (nativeCollarDivergenceFirst g) u.val x=_
  linarith only [hd,hp]

theorem nativeCollarDensityLaplacian_weak_ae (g : RiemannianMetric 3 E) (J : nativeCollarJetClosure) :
    (nativeCollarDensityLaplacianCLM g J.val : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weakSecondOrderPerturbation nativePoissonEntranceCollar
        (fun i j x => nativeDivergenceMatrix g x i j) (nativeCollarDivergenceFirst g) (fun _ => 0) J.val.1 :=
  nativeCollarJetPerturbation_weak_ae _ _ _ _ _ _ J

#print axioms nativeCollarDensityLaplacian_C2_ae
#print axioms nativeCollarDensityLaplacian_weak_ae
end Yamabe3.Analysis.SpherePolar
