import Yamabe3.Analysis.NativeC2CollarSeries
import Yamabe3.Analysis.L2SeriesNormBudget

/-! Uniform norm bounds for the same actual physical H2 series.
The constants are fixed by collar geometry before the modes and budget. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

theorem exists_nativeC2Collar_series_norm_bounds {ι : Type*} :
    ∃ (G : ℝ) (K : Fin 3 → ℝ),0≤G ∧ (∀ k,0≤K k) ∧
    ∀ (u : ι → E → ℝ) (hu : ∀ i,ContDiffOn ℝ 2 (u i) ({0}ᶜ : Set E))
    (a : ι → ℝ),Summable a → (∀ i,0≤a i) → ∀ C : ℝ,0≤C →
    (∀ s : Finset ι,
      ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ s,u i x)^2)+
        (∫ x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian (fun y => ∑ i ∈ s,u i y) x^2))≤
          C*(∑ i ∈ s,a i)) →
    ‖∑' i,nativeC2CollarValue (hu i)‖^2≤C*(∑' i,a i) ∧
    (∀ j,‖∑' i,nativeC2CollarFirst (hu i) j‖^2≤(G*C)*(∑' i,a i)) ∧
    (∀ k j,‖∑' i,nativeC2CollarSecond (hu i) k j‖^2≤(K k*C)*(∑' i,a i)) := by
  let O : Set E := {0}ᶜ
  let W := nativePolarTimeWindow (Ioo (-1) 1)
  let V := nativePoissonEntranceCollar
  have hO : IsOpen O := isClosed_singleton.isOpen_compl
  have hW := nativePolarTimeWindow_open 1
  have hWc := nativePolarTimeWindow_precompact 1
  have hWO := nativePolarTimeWindow_closure_offZero 1
  have hV : IsOpen V := nativePolarTimeWindow_open (1/2)
  have hVc := nativePolarTimeWindow_precompact (1/2)
  have hVW : closure V ⊆ W := nativePolarTimeWindow_nested (by norm_num : (1/2:ℝ)<1)
  have hVO : V ⊆ O := subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2))
  obtain ⟨G,hG,hgrad⟩ := exists_uniform_C2_local_gradient_estimate hO hW hWc hWO hV hVc hVW
  obtain ⟨K,hK,hhess⟩ := exists_uniform_C2_local_hessian_estimate hO hW hWc hWO hV hVc hVW
  refine ⟨G,K,hG,hK,?_⟩
  intro u hu a ha ha0 C hC he
  have hs (s : Finset ι) : ContDiffOn ℝ 2 (fun x => ∑ i ∈ s,u i x) O :=
    ContDiffOn.sum (fun i _ => hu i)
  refine ⟨?_,fun j => ?_,fun k j => ?_⟩
  · change ‖∑' i,(nativeC2Collar_memLp (hu i)).1.toLp (u i)‖^2≤_
    apply norm_L2_series_sq_le_of_finite_integrals _ _ ha hC
    intro s
    have hLp := native_memLp_two_of_continuousOn_precompact hW.measurableSet hWc hWO (hs s).continuousOn
    have hm := setIntegral_mono_set hLp.integrable_sq (Eventually.of_forall fun x => sq_nonneg (∑ i ∈ s,u i x))
      (Eventually.of_forall fun x hx => hVW (subset_closure hx))
    have hn : 0≤∫ x in W,nativeCoordinateLaplacian (fun y => ∑ i ∈ s,u i y) x^2 :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hb := he s
    change (∫ x in V,(∑ i ∈ s,u i x)^2)≤(∫ x in W,(∑ i ∈ s,u i x)^2) at hm
    linarith
  · change ‖∑' i,((nativeC2Collar_memLp (hu i)).2.1 j).toLp (nativeCoordinateFirst j (u i))‖^2≤_
    apply norm_L2_series_sq_le_of_finite_integrals _ _ ha (mul_nonneg hG hC)
    intro s
    have hae : (fun x => (∑ i ∈ s,nativeCoordinateFirst j (u i) x)^2)=ᵐ[volume.restrict V]
        (fun x => nativeCoordinateFirst j (fun y => ∑ i ∈ s,u i y) x^2) := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      rw [nativeCoordinateFirst_finite_sum s hO u (fun i _ => hu i) j (hVO hx)]
    rw [integral_congr_ae hae]
    have hLp := (nativeC2Collar_memLp (hs s)).2.1
    apply (integral_mono (hLp j).integrable_sq
      (integrable_finsetSum _ (fun l _ => (hLp l).integrable_sq))
      (fun x => Finset.single_le_sum (fun l _ => sq_nonneg (nativeCoordinateFirst l (fun y => ∑ i ∈ s,u i y) x))
        (Finset.mem_univ j))).trans
    exact (hgrad _ (hs s)).trans ((mul_le_mul_of_nonneg_left (he s) hG).trans_eq (by ring))
  · change ‖∑' i,((nativeC2Collar_memLp (hu i)).2.2 k j).toLp (nativeCoordinateSecond k j (u i))‖^2≤_
    apply norm_L2_series_sq_le_of_finite_eLpNorm_bound _ _ ha ha0 (mul_nonneg (hK k) hC)
    intro s
    have hae : (fun x => ∑ i ∈ s,nativeCoordinateSecond k j (u i) x)=ᵐ[volume.restrict V]
        nativeCoordinateSecond k j (fun y => ∑ i ∈ s,u i y) := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      exact (nativeCoordinateSecond_finite_sum s hO u (fun i _ => hu i) k j (hVO hx)).symm
    rw [eLpNorm_congr_ae hae]
    apply (hhess _ (hs s) k j).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    exact (mul_le_mul_of_nonneg_left (he s) (hK k)).trans_eq (by ring)

#print axioms exists_nativeC2Collar_series_norm_bounds
end Yamabe3.Analysis.SpherePolar
