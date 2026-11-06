import Yamabe3.Analysis.NativeFullZeroCompletion

/-! A uniform quantitative norm bound for the completion of the actual
low field after subtracting its actual finite entrance lift. The fixed
finite eigenvalue constants precede the orbit and original source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace InnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SpherePolar SphereSpectrum UniformElliptic
open Poincare.Analysis.Sobolev.Weak PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

def nativeLowZeroEnergyCoefficient : ℝ :=
  16*(nativeLowIndexFinset.card:ℝ)^2/6+
    (∑i∈nativeLowIndexFinset, (324+16*|angularEigenvalue i|))/4

theorem nativeLowZeroEnergyCoefficient_nonneg : 0≤nativeLowZeroEnergyCoefficient := by
  unfold nativeLowZeroEnergyCoefficient
  positivity

theorem nativeLowZeroCompletion_norm_sq (v:ℝ→ℝ) (hv:Continuous v)
    (hb:∀t,0≤v t ∧ v t≤1) (F:ℝ →ᵇ AngularL2) (z:H1Zero D O)
    (hz:(toL2 D O z:E→ℝ) =ᵐ[volume] (O).indicator (nativeLowZeroEntranceField v hv hb F)) :
    ‖z‖^2≤nativeLowZeroEnergyCoefficient*‖F‖^2 := by
  let q:=nativeLowZeroEntranceCoefficient v hv hb F
  let u:=nativeLowZeroEntranceField v hv hb F
  let du:Fin 3→E→ℝ:=fun i x=>fderiv ℝ u x (EuclideanSpace.single i 1)
  have hO:IsOpen O:=Metric.isOpen_ball.sdiff isClosed_singleton
  have hq (i:AngularIndex):ContDiff ℝ 2 (q i):=(nativeLowZeroEntranceCoefficient_C2_zero_bounds v hv hb F i).1
  have hq0 (i:AngularIndex) (t:ℝ):‖q i t‖≤(4*‖F‖)*Real.exp (-2*t):=
    ((nativeLowZeroEntranceCoefficient_C2_zero_bounds v hv hb F i).2.2 t).1
  have hq1 (i:AngularIndex) (t:ℝ):‖deriv (q i) t‖≤(16*‖F‖)*Real.exp (-2*t):=
    ((nativeLowZeroEntranceCoefficient_C2_zero_bounds v hv hb F i).2.2 t).2
  have hH:=finitePhysical_H1_of_exp_decay nativeLowIndexFinset q (fun i _=>hq i)
    (by positivity) (by positivity) (fun i _ t _=>hq0 i t) (fun i _ t _=>hq1 i t)
  have hD:=finitePhysical_gradient_L2_of_exp_decay nativeLowIndexFinset q (fun i _=>hq i)
    (by positivity) (by positivity) (fun i _ t _=>hq0 i t) (fun i _ t _=>hq1 i t)
  have hu0:=nativeLowZeroEntranceField_H01 v hv hb F
  have hC1:ContDiffOn ℝ 1 u O:=by
    rw [halfEnd_puncturedUnitBall_eq]
    exact (contDiffOn_finitePhysical_of_c2_positive nativeLowIndexFinset q
      (fun i _=>(hq i).contDiffOn)).of_le (by norm_num)
  have hn:=nativeEuclidean_memH01_norm_sq hO hu0 du hD.1
    (fun i=>native_hasWeakPartialDeriv_of_contDiffOn_one hO hC1 i) z hz
  rw [hn]
  have hi (i:Fin 3):Integrable (fun x=>du i x^2) (volume.restrict O):=(hD.1 i).integrable_sq
  rw [←integral_finsetSum Finset.univ (fun i _=>hi i)]
  calc
    _ ≤ ((nativeLowIndexFinset.card:ℝ)*(4*‖F‖))^2/6+
        (∑i∈nativeLowIndexFinset, ((16*‖F‖+4*‖F‖/2)^2+|angularEigenvalue i| *(4*‖F‖)^2))/4 :=
      add_le_add hH.2.1 hD.2
    _ = nativeLowZeroEnergyCoefficient*‖F‖^2 := by
      have hs:(∑i∈nativeLowIndexFinset,((16*‖F‖+4*‖F‖/2)^2+|angularEigenvalue i| *(4*‖F‖)^2))=
          (∑i∈nativeLowIndexFinset,(324+16*|angularEigenvalue i|))*‖F‖^2:=by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hs]
      unfold nativeLowZeroEnergyCoefficient
      ring

#print axioms nativeLowZeroEnergyCoefficient_nonneg
#print axioms nativeLowZeroCompletion_norm_sq
end Yamabe3.Analysis.Delaunay
