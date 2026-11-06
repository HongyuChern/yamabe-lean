import Yamabe3.Analysis.NativePoissonInfiniteH2Collar
import Yamabe3.Analysis.L2SeriesNormBudget

/-! Quantitative bounds for the actual infinite physical value, first derivatives
and Hessian entries; constants precede the boundary datum. The strong limits
are exactly the previously constructed same-curve H2 collar. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

theorem exists_nativePoissonCollar_H2_norm_bounds (P : NativeHighPotential) :
    ∃ (G : ℝ) (K : Fin 3 → ℝ),0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (b : AngularH1),NativeAngularSpectralRegular (3/2) (angularEmbedding b) →
      ‖nativePoissonCollarValue P b‖^2 ≤
        (12000*Real.exp 2*(4+P.derivativeBound))*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) ∧
      (∀ j,‖nativePoissonCollarFirst P b j‖^2 ≤
        G*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) ∧
      (∀ k j,‖nativePoissonCollarSecond P b k j‖^2 ≤
        K k*(∑' i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i)) := by
  obtain ⟨G,K,hG,hK,he⟩ := nativePoissonFiniteCollar_H2_estimates P
  refine ⟨G,K,hG,hK,?_⟩
  intro b hb
  let V := nativePoissonEntranceCollar
  let W := nativePolarTimeWindow (Ioo (-1) 1)
  have hV : IsOpen V := nativePolarTimeWindow_open (1/2)
  have hVW : V ⊆ W := subset_closure.trans (nativePolarTimeWindow_nested (by norm_num : (1/2:ℝ)<1))
  have hVO : V ⊆ ({0}ᶜ : Set E) := subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2))
  have ha0 (i : AngularIndex) : 0 ≤ nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := sq_nonneg _
  refine ⟨?_,fun j => ?_,fun k j => ?_⟩
  · unfold nativePoissonCollarValue nativePoissonCollarValueMode
    apply norm_L2_series_sq_le_of_finite_integrals _ _ hb
      (show 0 ≤ 12000*Real.exp 2*(4+P.derivativeBound) by have h:=P.derivativeBound_nonneg; positivity)
    intro s
    simp_rw [show ∀ x,(∑ i ∈ s,nativePoissonCollarMode P b i x)=nativePoissonFiniteCollar P b s x
      from fun x => congrFun (nativePoissonCollarMode_sum P b s) x]
    have h := nativePoissonFiniteCollar_finite_energy P b s
    have hm := setIntegral_mono_set h.2.1 (Eventually.of_forall fun x => sq_nonneg (nativePoissonFiniteCollar P b s x))
      (Eventually.of_forall fun x => @hVW x)
    have hn : 0 ≤ ∫ x in W,nativeCoordinateLaplacian (nativePoissonFiniteCollar P b s) x^2 :=
      integral_nonneg (fun x => sq_nonneg _)
    change (∫ x in V,nativePoissonFiniteCollar P b s x^2) ≤ (∫ x in W,nativePoissonFiniteCollar P b s x^2) at hm
    have hbnd := h.2.2.2
    change _ ≤ _
    linarith
  · unfold nativePoissonCollarFirst nativePoissonCollarFirstMode
    apply norm_L2_series_sq_le_of_finite_integrals _ _ hb hG
    intro s
    have hae : (fun x => (∑ i ∈ s,nativeCoordinateFirst j (nativePoissonCollarMode P b i) x)^2)
        =ᵐ[volume.restrict V] (fun x => nativeCoordinateFirst j (nativePoissonFiniteCollar P b s) x^2) := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      rw [nativePoissonCollarMode_first_sum P b s j (hVO hx)]
    rw [integral_congr_ae hae]
    have hLp (l : Fin 3) : MemLp (nativeCoordinateFirst l (nativePoissonFiniteCollar P b s)) 2 (volume.restrict V) :=
      native_C1_partials_memLp_on_precompact isClosed_singleton.isOpen_compl hV.measurableSet
        (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2))
        ((nativePoissonFiniteCollar_finite_energy P b s).1.of_le (by norm_num)) l
    apply (integral_mono (hLp j).integrable_sq
      (integrable_finsetSum _ (fun l _ => (hLp l).integrable_sq))
      (fun x => Finset.single_le_sum (fun l _ => sq_nonneg (nativeCoordinateFirst l (nativePoissonFiniteCollar P b s) x))
        (Finset.mem_univ j))).trans
    exact (he b s).1
  · unfold nativePoissonCollarSecond nativePoissonCollarSecondMode
    apply norm_L2_series_sq_le_of_finite_eLpNorm_bound _ _ hb ha0 (hK k)
    intro s
    have hae : (fun x => ∑ i ∈ s,nativeCoordinateSecond k j (nativePoissonCollarMode P b i) x)
        =ᵐ[volume.restrict V] nativeCoordinateSecond k j (nativePoissonFiniteCollar P b s) := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      exact nativePoissonCollarMode_second_sum P b s k j (hVO hx)
    rw [eLpNorm_congr_ae hae]
    exact (he b s).2 k j

#print axioms exists_nativePoissonCollar_H2_norm_bounds
end Yamabe3.Analysis.SpherePolar
