import Yamabe3.Analysis.NativeCollarTraceContinuity

/-! Canonical boundary limits: C2 families with the same strong volume
jets have the same value and radial derivative boundary limits. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

theorem native_C2_collar_memLp_jets {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    MemLp u 2 (volume.restrict nativePoissonEntranceCollar) ∧
    (∀ j,MemLp (nativeCoordinateFirst j u) 2 (volume.restrict nativePoissonEntranceCollar)) ∧
    (∀ k j,MemLp (nativeCoordinateSecond k j u) 2 (volume.restrict nativePoissonEntranceCollar)) := by
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hV := nativePolarTimeWindow_open (1/2)
  have hVc := nativePolarTimeWindow_precompact (1/2)
  have hVO := nativePolarTimeWindow_closure_offZero (1/2)
  have hp (j : Fin 3) : ContDiffOn ℝ 1 (nativeCoordinateFirst j u) {0}ᶜ :=
    (hu.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  exact ⟨native_memLp_two_of_continuousOn_precompact hV.measurableSet hVc hVO hu.continuousOn,
    fun j => native_memLp_two_of_continuousOn_precompact hV.measurableSet hVc hVO (hp j).continuousOn,
    fun k j => native_C1_partials_memLp_on_precompact hO hV.measurableSet hVc hVO (hp j) k⟩

theorem native_C2_collar_trace_difference_zero {ι : Type*} {l : Filter ι}
    (u v : ι → E → ℝ)
    (hu : ∀ a,ContDiffOn ℝ 2 (u a) ({0}ᶜ : Set E))
    (hv : ∀ a,ContDiffOn ℝ 2 (v a) ({0}ᶜ : Set E))
    (hvalue : Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,(u a x-v a x)^2) l (𝓝 0))
    (hfirst : ∀ j,Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,
      (nativeCoordinateFirst j (u a) x-nativeCoordinateFirst j (v a) x)^2) l (𝓝 0))
    (hsecond : ∀ k j,Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,
      (nativeCoordinateSecond k j (u a) x-nativeCoordinateSecond k j (v a) x)^2) l (𝓝 0)) :
    Tendsto (fun a => ∫ θ : S,(u a (θ:E)-v a (θ:E))^2 ∂angularVolume) l (𝓝 0) ∧
    Tendsto (fun a => ∫ θ : S,(fderiv ℝ (u a) (θ:E) (θ:E)-fderiv ℝ (v a) (θ:E) (θ:E))^2
      ∂angularVolume) l (𝓝 0) := by
  let z := fun a x => u a x-v a x
  have hz (a : ι) : ContDiffOn ℝ 2 (z a) ({0}ᶜ : Set E) := (hu a).sub (hv a)
  have hV : IsOpen nativePoissonEntranceCollar := nativePolarTimeWindow_open (1/2)
  have hVO : nativePoissonEntranceCollar ⊆ ({0}ᶜ : Set E) :=
    subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2))
  have hf (a : ι) (j : Fin 3) :
      (∫ x in nativePoissonEntranceCollar,nativeCoordinateFirst j (z a) x^2) =
      ∫ x in nativePoissonEntranceCollar,(nativeCoordinateFirst j (u a) x-nativeCoordinateFirst j (v a) x)^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [nativeCoordinateFirst_sub ((hu a).of_le (by norm_num)) ((hv a).of_le (by norm_num)) j (hVO hx)]
  have hs (a : ι) (k j : Fin 3) :
      (∫ x in nativePoissonEntranceCollar,nativeCoordinateSecond k j (z a) x^2) =
      ∫ x in nativePoissonEntranceCollar,(nativeCoordinateSecond k j (u a) x-nativeCoordinateSecond k j (v a) x)^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [nativeCoordinateSecond_sub (hu a) (hv a) k j (hVO hx)]
  have ht1 (j : Fin 3) : Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,nativeCoordinateFirst j (z a) x^2) l (𝓝 0) := by
    simpa only [hf] using hfirst j
  have ht2 (k j : Fin 3) : Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,nativeCoordinateSecond k j (z a) x^2) l (𝓝 0) := by
    simpa only [hs] using hsecond k j
  constructor
  · apply native_C1_collar_restriction_tendsto_zero z (fun a => (hz a).of_le (by norm_num))
    have he (a : ι) : (∫ x in nativePoissonEntranceCollar,z a x^2+∑ j : Fin 3,nativeCoordinateFirst j (z a) x^2) =
        (∫ x in nativePoissonEntranceCollar,z a x^2)+∑ j : Fin 3,∫ x in nativePoissonEntranceCollar,nativeCoordinateFirst j (z a) x^2 := by
      have hm := native_C2_collar_memLp_jets (hz a)
      rw [integral_add hm.1.integrable_sq (integrable_finsetSum _ (fun j _ => (hm.2.1 j).integrable_sq)),
        integral_finsetSum _ (fun j _ => (hm.2.1 j).integrable_sq)]
    simp_rw [he]
    simpa only [Finset.sum_const_zero,add_zero] using hvalue.add (tendsto_finset_sum _ (fun j _ => ht1 j))
  · have ht := native_C2_collar_normal_tendsto_zero z hz (by
      have he (a : ι) (j : Fin 3) : (∫ x in nativePoissonEntranceCollar,
          nativeCoordinateFirst j (z a) x^2+∑ k : Fin 3,nativeCoordinateSecond k j (z a) x^2) =
          (∫ x in nativePoissonEntranceCollar,nativeCoordinateFirst j (z a) x^2)+
          ∑ k : Fin 3,∫ x in nativePoissonEntranceCollar,nativeCoordinateSecond k j (z a) x^2 := by
        have hm := native_C2_collar_memLp_jets (hz a)
        rw [integral_add (hm.2.1 j).integrable_sq (integrable_finsetSum _ (fun k _ => (hm.2.2 k j).integrable_sq)),
          integral_finsetSum _ (fun k _ => (hm.2.2 k j).integrable_sq)]
      simp_rw [he]
      simpa only [Finset.sum_const_zero,add_zero] using
        tendsto_finset_sum Finset.univ (fun j _ => (ht1 j).add (tendsto_finset_sum _ (fun k _ => ht2 k j))))
    apply ht.congr'
    apply Eventually.of_forall
    intro a
    apply integral_congr_ae
    apply Eventually.of_forall
    intro θ
    have hx : (θ:E) ≠ 0 := by
      intro h
      have hn := norm_eq_of_mem_sphere θ
      rw [h,norm_zero] at hn
      norm_num at hn
    have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
    dsimp only [z]
    rw [fderiv_fun_sub (((hu a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num))
      (((hv a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num))]
    rfl

#print axioms native_C2_collar_memLp_jets
#print axioms native_C2_collar_trace_difference_zero
end Yamabe3.Analysis.SpherePolar
