import Yamabe3.Analysis.NativeC2SecondBudget
import Yamabe3.Analysis.FiniteRegularityExtension

/-! Genuine local Hessian control for C² functions by value and
Laplacian only. Cutoff and difference-quotient constants precede the
field; localization preserves every actual germ. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.NirenbergEuclidean

theorem exists_uniform_C2_compact_hessian_estimate
    {W V : Set E} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ K : Fin 3 → ℝ,(∀ k,0 ≤ K k) ∧
      ∀ u : E → ℝ,ContDiff ℝ 2 u → HasCompactSupport u → ∀ k i : Fin 3,
        eLpNorm (nativeCoordinateSecond k i u) 2 (volume.restrict V) ≤
          ENNReal.ofReal (Real.sqrt (K k*((∫ x in W,u x^2)+
            (∫ x in W,nativeCoordinateLaplacian u x^2)))) := by
  obtain ⟨U,C,hU,hUc,hVU,hUW,hC,hbound⟩ :=
    exists_uniform_C2_compact_second_budget hW hV hVc hVW
  obtain ⟨η,hη,hηc,hηrange,hηone,hηW,N,hN,hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hUc hW hUW
  let G : ℝ := 1+4*3*N^2
  let K : Fin 3 → ℝ := fun k => C k*(G+1)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  refine ⟨K,fun k => mul_nonneg (hC k) (by positivity),?_⟩
  intro u hu hc k i
  have hd := nativeCoordinateC2_compact_data hu hc
  have hUW' : U ⊆ W := subset_closure.trans hUW
  have hDη' : ∀ x (j : Fin 3),|fderiv ℝ η x (EuclideanSpace.single j 1)| ≤ N := by
    intro x j
    have h := (fderiv ℝ η x).le_opNorm (EuclideanSpace.single j 1)
    simp only [PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs] at h
    exact h.trans (hDη x)
  have hgrad := native_C1_gradient_integral_le hW hU.measurableSet hUW' hη hηc hηW
    (fun x => hηrange (mem_range_self x)) (fun x hx => hηone x (subset_closure hx)) hN hDη'
    (hu.of_le (by norm_num)).contDiffOn (hd.1.restrict W) (hd.2.2.1.restrict W)
    (fun j => (hd.2.1 j).restrict W) (nativeCoordinateLaplacian_weakEquation hW hu)
  simp only [neg_sq] at hgrad
  have hv := setIntegral_mono_set (hd.1.restrict W).integrable_sq
    (Eventually.of_forall (fun x => sq_nonneg (u x))) (Eventually.of_forall (fun x => @hUW' x))
  have hLap : MemLp (nativeCoordinateLaplacian u) 2 volume := by
    exact MemLp.ae_eq (Eventually.of_forall fun x => neg_neg (nativeCoordinateLaplacian u x)) hd.2.2.1.neg
  have hl := setIntegral_mono_set (hLap.restrict W).integrable_sq
    (Eventually.of_forall (fun x => sq_nonneg (nativeCoordinateLaplacian u x)))
    (Eventually.of_forall (fun x => @hUW' x))
  change (∫ x in U,u x^2) ≤ (∫ x in W,u x^2) at hv
  change (∫ x in U,nativeCoordinateLaplacian u x^2) ≤ (∫ x in W,nativeCoordinateLaplacian u x^2) at hl
  have hsum : ((∫ x in U,∑ j,nativeCoordinateFirst j u x^2)+
      (∫ x in U,u x^2)+(∫ x in U,nativeCoordinateLaplacian u x^2)) ≤
      (G+1)*((∫ x in W,u x^2)+(∫ x in W,nativeCoordinateLaplacian u x^2)) := by
    change (∫ x in U,∑ j : Fin 3,nativeCoordinateFirst j u x^2) ≤
      G*((∫ x in W,u x^2)+(∫ x in W,nativeCoordinateLaplacian u x^2)) at hgrad
    linarith only [hgrad,hv,hl]
  apply (hbound u hu hc k i).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  have h := mul_le_mul_of_nonneg_left hsum (hC k)
  simpa only [K,mul_assoc] using h

theorem exists_uniform_C2_local_hessian_estimate
    {O W V : Set E} (hO : IsOpen O) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWO : closure W ⊆ O) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVW : closure V ⊆ W) :
    ∃ K : Fin 3 → ℝ,(∀ k,0 ≤ K k) ∧
      ∀ u : E → ℝ,ContDiffOn ℝ 2 u O → ∀ k i : Fin 3,
        eLpNorm (nativeCoordinateSecond k i u) 2 (volume.restrict V) ≤
          ENNReal.ofReal (Real.sqrt (K k*((∫ x in W,u x^2)+
            (∫ x in W,nativeCoordinateLaplacian u x^2)))) := by
  obtain ⟨K,hK,h⟩ := exists_uniform_C2_compact_hessian_estimate hW hV hVc hVW
  refine ⟨K,hK,?_⟩
  intro u hu k i
  obtain ⟨v,hv,hvc,hvu⟩ := exists_finite_compact_extension_near_compact 2 hO hWc hWO hu
  have hVclW : V ⊆ closure W := (subset_closure.trans hVW).trans subset_closure
  have heV : nativeCoordinateSecond k i v =ᵐ[volume.restrict V] nativeCoordinateSecond k i u := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact nativeCoordinateSecond_congr_germ (hvu x (hVclW hx)) k i
  have he0 : (fun x => v x^2) =ᵐ[volume.restrict W] (fun x => u x^2) := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
    rw [(hvu x (subset_closure hx)).self_of_nhds]
  have he2 : (fun x => nativeCoordinateLaplacian v x^2) =ᵐ[volume.restrict W]
      (fun x => nativeCoordinateLaplacian u x^2) := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
    rw [nativeCoordinateLaplacian_congr_germ (hvu x (subset_closure hx))]
  have hb := h v hv hvc k i
  rwa [eLpNorm_congr_ae heV,integral_congr_ae he0,integral_congr_ae he2] at hb

#print axioms exists_uniform_C2_compact_hessian_estimate
#print axioms exists_uniform_C2_local_hessian_estimate
end Yamabe3.Analysis.SpherePolar
