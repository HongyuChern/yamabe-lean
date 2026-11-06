import Yamabe3.Analysis.NativePoissonCollarModes

/-! A genuine H2 collar sum from C2 physical modes and finite
value/Laplacian energy budgets. First and second derivatives are actual
coordinate derivatives; their limits are constructed by L2 completeness. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeC2Collar_memLp {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
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

def nativeC2CollarValue {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) := (nativeC2Collar_memLp hu).1.toLp u
def nativeC2CollarFirst {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) (j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ((nativeC2Collar_memLp hu).2.1 j).toLp (nativeCoordinateFirst j u)
def nativeC2CollarSecond {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) (k j : Fin 3) :
    Lp ℝ 2 (volume.restrict nativePoissonEntranceCollar) :=
  ((nativeC2Collar_memLp hu).2.2 k j).toLp (nativeCoordinateSecond k j u)

theorem nativeC2Collar_weak_jets {u : E → ℝ} (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) :
    (∀ j,HasWeakPartialDeriv j (nativeC2CollarFirst hu j) (nativeC2CollarValue hu) nativePoissonEntranceCollar) ∧
    (∀ k j,HasWeakPartialDeriv k (nativeC2CollarSecond hu k j) (nativeC2CollarFirst hu j) nativePoissonEntranceCollar) := by
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hV : IsOpen nativePoissonEntranceCollar := nativePolarTimeWindow_open (1/2)
  have hVO : nativePoissonEntranceCollar ⊆ ({0}ᶜ : Set E) :=
    subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2))
  have hp (j : Fin 3) : ContDiffOn ℝ 1 (nativeCoordinateFirst j u) {0}ᶜ :=
    (hu.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  constructor
  · intro j
    apply native_weakPartial_transfer_ae (nativeC2Collar_memLp hu).1.coeFn_toLp
      ((nativeC2Collar_memLp hu).2.1 j).coeFn_toLp
    exact native_hasWeakPartialDeriv_of_contDiffOn_one hV ((hu.of_le (by norm_num)).mono hVO) j
  · intro k j
    apply native_weakPartial_transfer_ae ((nativeC2Collar_memLp hu).2.1 j).coeFn_toLp
      ((nativeC2Collar_memLp hu).2.2 k j).coeFn_toLp
    exact native_hasWeakPartialDeriv_of_contDiffOn_one hV ((hp j).mono hVO) k

theorem nativeC2Collar_series_summable {ι : Type*} (u : ι → E → ℝ)
    (hu : ∀ i,ContDiffOn ℝ 2 (u i) ({0}ᶜ : Set E))
    {a : ι → ℝ} (ha : Summable a) (ha0 : ∀ i,0≤a i) {C : ℝ} (hC : 0≤C)
    (he : ∀ s : Finset ι,
      ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ s,u i x)^2)+
        (∫ x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian (fun y => ∑ i ∈ s,u i y) x^2))≤
          C*(∑ i ∈ s,a i)) :
    Summable (fun i => nativeC2CollarValue (hu i)) ∧
      (∀ j,Summable (fun i => nativeC2CollarFirst (hu i) j)) ∧
      (∀ k j,Summable (fun i => nativeC2CollarSecond (hu i) k j)) := by
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
  have hs (s : Finset ι) : ContDiffOn ℝ 2 (fun x => ∑ i ∈ s,u i x) O :=
    ContDiffOn.sum (fun i _ => hu i)
  obtain ⟨G,hG,hgrad⟩ := exists_uniform_C2_local_gradient_estimate hO hW hWc hWO hV hVc hVW
  obtain ⟨K,hK,hhess⟩ := exists_uniform_C2_local_hessian_estimate hO hW hWc hWO hV hVc hVW
  refine ⟨?_,fun j => ?_,fun k j => ?_⟩
  · change Summable (fun i => (nativeC2Collar_memLp (hu i)).1.toLp (u i))
    apply exists_L2_sum_of_finite_square_integrals _ _ ha hC
    intro s
    have hLp := native_memLp_two_of_continuousOn_precompact hW.measurableSet hWc hWO (hs s).continuousOn
    have hm := setIntegral_mono_set hLp.integrable_sq (Eventually.of_forall fun x => sq_nonneg (∑ i ∈ s,u i x))
      (Eventually.of_forall fun x hx => hVW (subset_closure hx))
    have hn : 0≤∫ x in W,nativeCoordinateLaplacian (fun y => ∑ i ∈ s,u i y) x^2 :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hb := he s
    change (∫ x in V,(∑ i ∈ s,u i x)^2)≤(∫ x in W,(∑ i ∈ s,u i x)^2) at hm
    linarith
  · change Summable (fun i => ((nativeC2Collar_memLp (hu i)).2.1 j).toLp (nativeCoordinateFirst j (u i)))
    apply exists_L2_sum_of_finite_square_integrals _ _ ha (mul_nonneg hG hC)
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
  · change Summable (fun i => ((nativeC2Collar_memLp (hu i)).2.2 k j).toLp (nativeCoordinateSecond k j (u i)))
    apply summable_L2_of_finite_eLpNorm_bound _ _ ha ha0 (mul_nonneg (hK k) hC)
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

theorem nativeC2Collar_series_H2 {ι : Type*} (u : ι → E → ℝ)
    (hu : ∀ i,ContDiffOn ℝ 2 (u i) ({0}ᶜ : Set E))
    {a : ι → ℝ} (ha : Summable a) (ha0 : ∀ i,0≤a i) {C : ℝ} (hC : 0≤C)
    (he : ∀ s : Finset ι,
      ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ s,u i x)^2)+
        (∫ x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian (fun y => ∑ i ∈ s,u i y) x^2))≤
          C*(∑ i ∈ s,a i)) :
    MemWkp 2 2 (⇑(∑' i,nativeC2CollarValue (hu i))) nativePoissonEntranceCollar ∧
      (∀ j,HasWeakPartialDeriv j (⇑(∑' i,nativeC2CollarFirst (hu i) j))
        (⇑(∑' i,nativeC2CollarValue (hu i))) nativePoissonEntranceCollar) ∧
      (∀ k j,HasWeakPartialDeriv k (⇑(∑' i,nativeC2CollarSecond (hu i) k j))
        (⇑(∑' i,nativeC2CollarFirst (hu i) j)) nativePoissonEntranceCollar) := by
  have h := nativeC2Collar_series_summable u hu ha ha0 hC he
  exact native_memWkp_two_Lp_series (nativePolarTimeWindow_open (1/2))
    (fun i => nativeC2CollarValue (hu i)) (fun j i => nativeC2CollarFirst (hu i) j)
    (fun k j i => nativeC2CollarSecond (hu i) k j) h.1 h.2.1 h.2.2
    (fun a j => (nativeC2Collar_weak_jets (hu a)).1 j)
    (fun a k j => (nativeC2Collar_weak_jets (hu a)).2 k j)

#print axioms nativeC2Collar_memLp
#print axioms nativeC2Collar_weak_jets
#print axioms nativeC2Collar_series_summable
#print axioms nativeC2Collar_series_H2
end Yamabe3.Analysis.SpherePolar
