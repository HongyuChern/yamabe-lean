import Yamabe3.Analysis.NativeFullCollarJetError
import Yamabe3.Analysis.NativeCollarPotentialMultiplier
import Yamabe3.Analysis.NativeDelaunayHalfEndPotential

/-! The actual native rescaled Jacobian as a continuous operator on the
true collar jet. Its same-orbit potential, negative divergence, density
and scalar curvature are identified on every off-origin C2 function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem principalSource_identity_coordinate (u : E → ℝ) (x : E) :
    principalSource (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ)) u x= -nativeCoordinateLaplacian u x := by
  have hf : matrixFlux (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (fun j => partialDeriv j u)=fun j => partialDeriv j u := by
    funext i y
    simp [matrixFlux,Matrix.one_apply]
  simp only [principalSource,hf,nativeCoordinateLaplacian,partialDeriv]
  rfl

theorem nativeDelaunayOperatorError_eq_difference_C2
    (g : RiemannianMetric 3 E) {r : ℝ} (hr : 0<r) (v : ℝ → ℝ) (phase : ℝ)
    {u : E → ℝ} {x : E} (hx : x≠0) (hu : ContDiffAt ℝ 2 u x) :
    nativeDelaunayOperatorError g r v phase u x=
      nativeRescaledDelaunayJacobian g r v phase u x-flatDelaunayJacobian v phase u x := by
  have hc := principalSource_sub_coefficients_C2_at
    (fun y => nativeDivergenceMatrix g (r • y)) (fun _ => 1)
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r))
    (fun _ _ => contDiff_const) hu
  rw [nativeDelaunayOperatorError,nativeScaledGeometricError_eq_negative_principalSource_C2_at g r x hu,
    neg_neg,hc,nativeRescaledDelaunayJacobian,
    rescaledNativeJacobianPotential_delaunay g hr v phase hx,flatDelaunayJacobian]
  ring

def nativeFlatCollarJetCLM (V : ℝ →ᵇ ℝ) : NativeCollarJet →L[ℝ] NativeCollarL2 :=
  -((∑ j : Fin 3,nativeCollarJetSecondCLM j j)+
    (nativeCollarPotentialMulCLM V).comp nativeCollarJetValueCLM)

theorem nativeFlatCollarJet_C2_ae (V : ℝ →ᵇ ℝ) (u : nativeC2OffZero) :
    (nativeFlatCollarJetCLM V (nativeC2CollarJetLinear u) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => -nativeCoordinateLaplacian u.val x-nativeHalfEndPotentialCoefficient V x*u.val x) := by
  let L := ∑ j : Fin 3,nativeC2CollarSecond u.property j j
  let U := nativeC2CollarValue u.property
  have hsum : (L : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] nativeCoordinateLaplacian u.val := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => nativeC2CollarSecond u.property j j),
      (ae_all_iff).mpr (fun j => ((nativeC2Collar_memLp u.property).2.2 j j).coeFn_toLp)] with x hs hj
    change L x=_
    rw [hs]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hj j)
  change (⇑(-(L+nativeCollarPotentialMulCLM V U)))=ᵐ[_] _
  filter_upwards [Lp.coeFn_neg (L+nativeCollarPotentialMulCLM V U),
    Lp.coeFn_add L (nativeCollarPotentialMulCLM V U),hsum,
    nativeCollarPotentialMulCLM_ae V U,(nativeC2Collar_memLp u.property).1.coeFn_toLp] with x hn ha hl hp hu
  rw [hn]
  simp only [Pi.neg_apply]
  rw [ha]
  change -(L x+nativeCollarPotentialMulCLM V U x)=_
  rw [hl,hp]
  have hv : (U : E → ℝ) x=u.val x := hu
  rw [hv]
  ring

def nativeOrbitCollarJacobianCLM (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (hb : ∀ t,0≤v t ∧ v t≤1) (phase : ℝ) :
    NativeCollarJet →L[ℝ] NativeCollarL2 :=
  nativeFlatCollarJetCLM (delaunayPhasePotentialBCF v hv.continuous hb phase)+
    nativeFullCollarJetErrorCLM g r v hv phase

theorem nativeOrbitCollarJacobian_C2_ae (g : RiemannianMetric 3 E) {r : ℝ} (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (hb : ∀ t,0≤v t ∧ v t≤1) (phase : ℝ)
    (u : nativeC2OffZero) :
    (nativeOrbitCollarJacobianCLM g r v hv hb phase (nativeC2CollarJetLinear u) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeRescaledDelaunayJacobian g r v phase u.val := by
  let V := delaunayPhasePotentialBCF v hv.continuous hb phase
  let J := nativeC2CollarJetLinear u
  have hQ (x : E) : nativeHalfEndPotentialCoefficient V x= -annularDelaunayPotential v phase x := by
    change (15/4)*v (-Real.log ‖x‖+phase)^4/‖x‖^2= -(-(15/4)*v (phase-Real.log ‖x‖)^4/‖x‖^2)
    rw [show -Real.log ‖x‖+phase=phase-Real.log ‖x‖ by ring]
    ring
  filter_upwards [Lp.coeFn_add (nativeFlatCollarJetCLM V J) (nativeFullCollarJetErrorCLM g r v hv phase J),
    nativeFlatCollarJet_C2_ae V u,nativeFullCollarJetError_C2_ae g r v hv phase u,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hadd hflat herr hx
  change (nativeFlatCollarJetCLM V J+nativeFullCollarJetErrorCLM g r v hv phase J : NativeCollarL2) x=_
  rw [hadd]
  change nativeFlatCollarJetCLM V J x+nativeFullCollarJetErrorCLM g r v hv phase J x=_
  rw [hflat,herr,hQ]
  have hx0 := (nativeEntranceCollar_subset_shell hx)
  have hux := u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds (cylinderShell_ne_zero hx0))
  rw [nativeDelaunayOperatorError_eq_difference_C2 g hr v phase (cylinderShell_ne_zero hx0) hux,
    flatDelaunayJacobian,principalSource_identity_coordinate]
  ring

#print axioms principalSource_identity_coordinate
#print axioms nativeDelaunayOperatorError_eq_difference_C2
#print axioms nativeFlatCollarJet_C2_ae
#print axioms nativeOrbitCollarJacobian_C2_ae
end Yamabe3.Analysis.SpherePolar
