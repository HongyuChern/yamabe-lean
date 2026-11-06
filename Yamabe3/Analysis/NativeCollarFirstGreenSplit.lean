import Yamabe3.Analysis.NativeCollarWeakFirstGreen

/-! Both orientations of first-order Green on the same volume jet. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem nativeCollar_test_integrable (φ : E → ℝ) (hφ : Continuous φ) (F : NativeCollarL2) :
    Integrable (fun x => φ x*(F : E → ℝ) x) (volume.restrict nativePoissonEntranceCollar) := by
  have hm : MemLp φ 2 (volume.restrict nativePoissonEntranceCollar) :=
    native_memLp_two_of_continuousOn_precompact (nativePolarTimeWindow_open (1/2)).measurableSet
      (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2)) hφ.continuousOn
  exact hm.integrable_mul (Lp.memLp F)

theorem nativeCollar_ball_compl_ae :
    (ball (0:E) 1)ᶜ =ᵐ[volume.restrict nativePoissonEntranceCollar] {x : E | 1<‖x‖} := by
  have hn : ∀ᵐ x : E ∂volume,x∉sphere (0:E) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0:E) 1)
  filter_upwards [ae_mono Measure.restrict_le_self hn] with x hx
  apply propext
  have hne : ‖x‖≠1 := by simpa only [mem_sphere,dist_zero_right] using hx
  change (x∉ball (0:E) 1) ↔ 1<‖x‖
  simp only [mem_ball,dist_zero_right,not_lt]
  exact le_iff_lt_or_eq.trans (or_iff_left hne.symm)

theorem nativeCollar_integral_split {H : E → ℝ}
    (hH : Integrable H (volume.restrict nativePoissonEntranceCollar)) :
    (∫x in nativePoissonEntranceCollar ∩ ball 0 1,H x)+
      (∫x in nativePoissonEntranceCollar ∩ {y : E | 1<‖y‖},H x)=
      ∫x in nativePoissonEntranceCollar,H x := by
  have h := integral_add_compl (μ := volume.restrict nativePoissonEntranceCollar)
    (s := ball (0:E) 1) isOpen_ball.measurableSet hH
  rw [setIntegral_congr_set (f := H) nativeCollar_ball_compl_ae] at h
  simpa only [Measure.restrict_restrict isOpen_ball.measurableSet,
    Measure.restrict_restrict (isOpen_lt continuous_const continuous_norm).measurableSet,inter_comm] using h

theorem nativeCollarFirstGreen_total_zero (ψ : E → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆nativePoissonEntranceCollar)
    (j : Fin 3) (J : nativeCollarJetClosure) :
    nativeCollarFirstGreenRegionCLM univ MeasurableSet.univ ψ (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) j J.val=0 := by
  rw [nativeCollarFirstGreenRegion_eq_integral,inter_univ,
    integral_add (nativeCollar_test_integrable _ (native_partial_test_continuous (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) j) _)
      (nativeCollar_test_integrable _ hψ.continuous _)]
  have hw := (nativeCollarJetClosure_weak_jets J).1 j ψ hψ hc hs
  have he : (∫x in nativePoissonEntranceCollar,partialDeriv j ψ x*(J.val.1 : E → ℝ) x)=
      -(∫x in nativePoissonEntranceCollar,ψ x*(J.val.2.1 j : E → ℝ) x) := by
    simpa only [partialDeriv,mul_comm] using hw
  rw [he,neg_add_cancel]

theorem nativeCollarFirstGreen_volume_split (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (j : Fin 3) (J : NativeCollarJet) :
    nativeCollarFirstGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet ψ hψ j J+
      nativeCollarFirstGreenRegionCLM {x : E | 1<‖x‖} (isOpen_lt continuous_const continuous_norm).measurableSet ψ hψ j J=
      nativeCollarFirstGreenRegionCLM univ MeasurableSet.univ ψ hψ j J := by
  simp only [nativeCollarFirstGreenRegion_eq_integral,inter_univ]
  exact nativeCollar_integral_split ((nativeCollar_test_integrable _ (native_partial_test_continuous hψ j) _).add
    (nativeCollar_test_integrable _ hψ.continuous _))

theorem nativeCollarWeakFirstGreen_interior (ψ : E → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆nativePoissonEntranceCollar)
    (j : Fin 3) (J : nativeCollarJetClosure) :
    nativeCollarFirstGreenRegionCLM (ball 0 1) isOpen_ball.measurableSet ψ (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) j J.val=
      nativeCollarValueNormalPairCLM ψ hψ.continuous j J := by
  have h := nativeCollarFirstGreen_volume_split ψ (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) j J.val
  rw [nativeCollarFirstGreen_total_zero ψ hψ hc hs j J,
    nativeCollarWeakFirstGreen_exterior ψ (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hc hs j J] at h
  linarith only [h]

#print axioms nativeCollar_test_integrable
#print axioms nativeCollar_ball_compl_ae
#print axioms nativeCollar_integral_split
#print axioms nativeCollarFirstGreen_total_zero
#print axioms nativeCollarFirstGreen_volume_split
#print axioms nativeCollarWeakFirstGreen_interior
end Yamabe3.Analysis.SpherePolar
