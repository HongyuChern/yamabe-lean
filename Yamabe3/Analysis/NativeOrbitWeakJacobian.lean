import Yamabe3.Analysis.NativeOrbitCollarJacobian
import Yamabe3.Analysis.WeakLaplacianDilation

/-! The collar operator is identified with the weak coordinate operator
of its own value, using first and second weak-derivative uniqueness. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

def nativeWeakRescaledDelaunayJacobian (O : Set E) (g : RiemannianMetric 3 E)
    (r : ℝ) (v : ℝ → ℝ) (phase : ℝ) (u : E → ℝ) : E → ℝ := fun x =>
  weakNegativeLaplacian O u x+annularDelaunayPotential v phase x*u x-
    weakSecondOrderPerturbation O (nativeScaledPrincipalError g r) (nativeScaledFirstError g r) (fun _ => 0) u x+
    nativeDelaunayPotentialError g r v phase x*u x

theorem nativeWeakRescaledDelaunayJacobian_congr {O : Set E} (hO : IsOpen O)
    (g : RiemannianMetric 3 E) (r : ℝ) (v : ℝ → ℝ) (phase : ℝ)
    {u z : E → ℝ} (he : u=ᵐ[volume.restrict O] z) :
    nativeWeakRescaledDelaunayJacobian O g r v phase u=ᵐ[volume.restrict O]
      nativeWeakRescaledDelaunayJacobian O g r v phase z := by
  have h1 (j : Fin 3) := chosenWeakPartial'_ae_congr (by norm_num : (1:ℝ≥0∞)≤2) hO he j
  have h2 (i j : Fin 3) := chosenWeakPartial'_ae_congr (by norm_num : (1:ℝ≥0∞)≤2) hO (h1 j) i
  filter_upwards [he,eventually_all.mpr h1,eventually_all.mpr (fun i => eventually_all.mpr (h2 i))] with x hx h1 h2
  simp only [nativeWeakRescaledDelaunayJacobian,weakNegativeLaplacian,iterWeakPartial,weakSecondOrderPerturbation,hx,h1,h2]

theorem nativeFlatCollarJet_weak_ae (V : ℝ →ᵇ ℝ) (J : nativeCollarJetClosure) :
    (nativeFlatCollarJetCLM V J.val : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => weakNegativeLaplacian nativePoissonEntranceCollar J.val.1 x-
        nativeHalfEndPotentialCoefficient V x*J.val.1 x) := by
  let L := ∑j : Fin 3,J.val.2.2 j j
  let U := J.val.1
  have hj := nativeCollarJetClosure_chosen_jets J
  have hs : (L : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => ∑j : Fin 3,chosenWeakPartial' 2 j (chosenWeakPartial' 2 j U nativePoissonEntranceCollar) nativePoissonEntranceCollar x) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => J.val.2.2 j j),
      eventually_all.mpr (fun j => hj.2 j j)] with x hs hd
    change (∑j : Fin 3,J.val.2.2 j j : NativeCollarL2) x=_
    rw [hs]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => (hd j).symm)
  change (⇑(-(L+nativeCollarPotentialMulCLM V U)))=ᵐ[_] _
  filter_upwards [Lp.coeFn_neg (L+nativeCollarPotentialMulCLM V U),
    Lp.coeFn_add L (nativeCollarPotentialMulCLM V U),hs,nativeCollarPotentialMulCLM_ae V U] with x hn ha hs hp
  change (-((L+nativeCollarPotentialMulCLM V U)) : NativeCollarL2) x=_
  rw [hn]
  change -((L+nativeCollarPotentialMulCLM V U) x)=_
  rw [ha]
  change -(L x+nativeCollarPotentialMulCLM V U x)=_
  rw [hs,hp]
  simp only [weakNegativeLaplacian,iterWeakPartial]
  ring

theorem nativeOrbitCollarJacobian_weak_ae (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (hb : ∀t,0≤v t ∧ v t≤1) (phase : ℝ)
    (J : nativeCollarJetClosure) :
    (nativeOrbitCollarJacobianCLM g r v hv hb phase J.val : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar g r v phase J.val.1 := by
  let V := delaunayPhasePotentialBCF v hv.continuous hb phase
  have hQ (x : E) : nativeHalfEndPotentialCoefficient V x= -annularDelaunayPotential v phase x := by
    change (15/4)*v (-Real.log ‖x‖+phase)^4/‖x‖^2= -(-(15/4)*v (phase-Real.log ‖x‖)^4/‖x‖^2)
    rw [show -Real.log ‖x‖+phase=phase-Real.log ‖x‖ by ring]
    ring
  filter_upwards [Lp.coeFn_add (nativeFlatCollarJetCLM V J.val) (nativeFullCollarJetErrorCLM g r v hv phase J.val),
    nativeFlatCollarJet_weak_ae V J,nativeFullCollarJetError_weak_ae g r v hv phase J] with x ha hf he
  change (nativeFlatCollarJetCLM V J.val+nativeFullCollarJetErrorCLM g r v hv phase J.val : NativeCollarL2) x=_
  rw [ha]
  change nativeFlatCollarJetCLM V J.val x+nativeFullCollarJetErrorCLM g r v hv phase J.val x=_
  rw [hf,he,hQ]
  dsimp only [nativeWeakRescaledDelaunayJacobian]
  ring

theorem nativeWeakRescaledDelaunayJacobian_C2_ae (g : RiemannianMetric 3 E) {r : ℝ} (hr : 0<r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (hb : ∀t,0≤v t ∧ v t≤1) (phase : ℝ)
    (u : nativeC2OffZero) :
    nativeWeakRescaledDelaunayJacobian nativePoissonEntranceCollar g r v phase u.val=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeRescaledDelaunayJacobian g r v phase u.val := by
  let J : nativeCollarJetClosure := ⟨nativeC2CollarJetLinear u,subset_closure ⟨u,rfl⟩⟩
  have hj := nativeOrbitCollarJacobian_weak_ae g r v hv hb phase J
  have he := nativeWeakRescaledDelaunayJacobian_congr (nativePolarTimeWindow_open (1/2)) g r v phase
    (nativeC2Collar_memLp u.property).1.coeFn_toLp
  exact he.symm.trans (hj.symm.trans (nativeOrbitCollarJacobian_C2_ae g hr v hv hb phase u))

#print axioms nativeWeakRescaledDelaunayJacobian_congr
#print axioms nativeFlatCollarJet_weak_ae
#print axioms nativeOrbitCollarJacobian_weak_ae
#print axioms nativeWeakRescaledDelaunayJacobian_C2_ae
end Yamabe3.Analysis.SpherePolar
