import Yamabe3.Analysis.NativeH4GraphAllScaleJet
import Yamabe3.Analysis.NativeAllScaleLocalH2
import Yamabe3.Analysis.SobolevLocalCompactExtension

/-! Positive physical scales suffice for local H2 regularity in the
punctured unit ball. This does not require, or assert, a negative-scale
extension of the half-end graph beyond its actual index range. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem native_true_scale_jet_physical_H2 (s : ℝ) (J : nativeCollarJetClosure) {u : E→ℝ}
    (he : (J.val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))) :
    MemWkp 2 2 u (nativePhysicalScaleWindow s) := by
  apply native_scaled_H2_to_physical s
  exact (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) he).mp
    (nativeCollarJetClosure_memH2 J)

theorem native_positive_scale_H2_local {u : E→ℝ}
    (h : ∀s : ℝ,0 ≤ s → MemWkp 2 2 u (nativePhysicalScaleWindow s)) :
    MemWkpLocally 2 u (Metric.ball 0 1 \ {(0:E)}) := by
  intro x hx
  have hx0 : x≠0 := by simpa only [mem_singleton_iff] using hx.2
  have hx1 : ‖x‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hx.1
  have hs : 0 ≤ -Real.log ‖x‖ := neg_nonneg.mpr (Real.log_nonpos (norm_nonneg x) hx1.le)
  let W := nativePhysicalScaleWindow (-Real.log ‖x‖)
  have hW := nativePhysicalScaleWindow_open (-Real.log ‖x‖)
  have hO : IsOpen (Metric.ball 0 1 \ {(0:E)}) := Metric.isOpen_ball.sdiff isClosed_singleton
  refine ⟨W∩(Metric.ball 0 1 \ {(0:E)}),hW.inter hO,
    ⟨nativePhysicalScaleWindow_covers hx0,hx⟩,inter_subset_right,?_⟩
  exact (h _ hs).mono_set (by norm_num) (hW.inter hO) inter_subset_left

theorem native_half_scale_jet_local_H2 (J : HalfEndPhysicalSliceIndex→nativeCollarJetClosure) {u : E→ℝ}
    (he : ∀i,(J i).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*i.1/2)*u (Real.exp (-i.1) • x))) :
    MemWkpLocally 2 u (Metric.ball 0 1 \ {(0:E)}) := by
  apply native_positive_scale_H2_local
  intro s hs
  let i : HalfEndPhysicalSliceIndex := ⟨s,(neg_nonpos.mpr (Real.log_nonneg (by norm_num))).trans hs⟩
  exact native_true_scale_jet_physical_H2 s (J i) (he i)

#print axioms native_true_scale_jet_physical_H2
#print axioms native_positive_scale_H2_local
#print axioms native_half_scale_jet_local_H2
end Yamabe3.Analysis.SpherePolar
