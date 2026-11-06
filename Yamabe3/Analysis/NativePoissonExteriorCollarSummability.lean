import Yamabe3.Analysis.NativePoissonExteriorCollarModes

/-! Strong L2 summability of the actual physical values, first derivatives,
and Hessian entries, from the finite collar estimates at the 3/2 scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

theorem nativePoissonExteriorCollar_modes_summable (P : NativeHighPotential) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    Summable (nativePoissonExteriorCollarValueMode P b) ∧
      (∀ j,Summable (nativePoissonExteriorCollarFirstMode P b j)) ∧
      (∀ k j,Summable (nativePoissonExteriorCollarSecondMode P b k j)) := by
  let V := nativePoissonEntranceCollar
  let W := nativePolarTimeWindow (Ioo (-1) 1)
  have hV : IsOpen V := nativePolarTimeWindow_open (1/2)
  have hVW : V ⊆ W := subset_closure.trans (nativePolarTimeWindow_nested (by norm_num : (1/2:ℝ)<1))
  have hVO : V ⊆ ({0}ᶜ : Set E) := subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2))
  have ha0 (i : AngularIndex) : 0 ≤ nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := sq_nonneg _
  obtain ⟨G,K,hG,hK,he⟩ := nativePoissonExteriorFiniteCollar_H2_estimates P
  refine ⟨?_,fun j => ?_,fun k j => ?_⟩
  · change Summable (fun i => (nativePoissonExteriorCollarMode_memLp P b i).1.toLp (nativePoissonExteriorCollarMode P b i))
    apply exists_L2_sum_of_finite_square_integrals _ _ hb
      (show 0 ≤ 12000*Real.exp 2*(4+P.derivativeBound) by have h:=P.derivativeBound_nonneg; positivity)
    intro s
    simp_rw [show ∀ x,(∑ i ∈ s,nativePoissonExteriorCollarMode P b i x)=nativePoissonExteriorFiniteCollar P b s x
      from fun x => congrFun (nativePoissonExteriorCollarMode_sum P b s) x]
    have h := nativePoissonExteriorFiniteCollar_finite_energy P b s
    have hm := setIntegral_mono_set h.2.1 (Eventually.of_forall fun x => sq_nonneg (nativePoissonExteriorFiniteCollar P b s x))
      (Eventually.of_forall fun x => @hVW x)
    have hn : 0 ≤ ∫ x in W,nativeCoordinateLaplacian (nativePoissonExteriorFiniteCollar P b s) x^2 :=
      integral_nonneg (fun x => sq_nonneg _)
    change (∫ x in V,nativePoissonExteriorFiniteCollar P b s x^2) ≤ (∫ x in W,nativePoissonExteriorFiniteCollar P b s x^2) at hm
    have hbnd := h.2.2.2
    change _ ≤ _
    linarith
  · change Summable (fun i => ((nativePoissonExteriorCollarMode_memLp P b i).2.1 j).toLp
      (nativeCoordinateFirst j (nativePoissonExteriorCollarMode P b i)))
    apply exists_L2_sum_of_finite_square_integrals _ _ hb hG
    intro s
    have hae : (fun x => (∑ i ∈ s,nativeCoordinateFirst j (nativePoissonExteriorCollarMode P b i) x)^2)
        =ᵐ[volume.restrict V] (fun x => nativeCoordinateFirst j (nativePoissonExteriorFiniteCollar P b s) x^2) := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      rw [nativePoissonExteriorCollarMode_first_sum P b s j (hVO hx)]
    rw [integral_congr_ae hae]
    have hLp (l : Fin 3) : MemLp (nativeCoordinateFirst l (nativePoissonExteriorFiniteCollar P b s)) 2 (volume.restrict V) :=
      native_C1_partials_memLp_on_precompact isClosed_singleton.isOpen_compl hV.measurableSet
        (nativePolarTimeWindow_precompact (1/2)) (nativePolarTimeWindow_closure_offZero (1/2))
        ((nativePoissonExteriorFiniteCollar_finite_energy P b s).1.of_le (by norm_num)) l
    apply (integral_mono (hLp j).integrable_sq
      (integrable_finsetSum _ (fun l _ => (hLp l).integrable_sq))
      (fun x => Finset.single_le_sum (fun l _ => sq_nonneg (nativeCoordinateFirst l (nativePoissonExteriorFiniteCollar P b s) x))
        (Finset.mem_univ j))).trans
    exact (he b s).1
  · change Summable (fun i => ((nativePoissonExteriorCollarMode_memLp P b i).2.2 k j).toLp
      (nativeCoordinateSecond k j (nativePoissonExteriorCollarMode P b i)))
    apply summable_L2_of_finite_eLpNorm_bound _ _ hb ha0 (hK k)
    intro s
    have hae : (fun x => ∑ i ∈ s,nativeCoordinateSecond k j (nativePoissonExteriorCollarMode P b i) x)
        =ᵐ[volume.restrict V] nativeCoordinateSecond k j (nativePoissonExteriorFiniteCollar P b s) := by
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      exact nativePoissonExteriorCollarMode_second_sum P b s k j (hVO hx)
    rw [eLpNorm_congr_ae hae]
    exact (he b s).2 k j

#print axioms nativePoissonExteriorCollar_modes_summable
end Yamabe3.Analysis.SpherePolar
