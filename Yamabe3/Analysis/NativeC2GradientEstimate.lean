import Yamabe3.Analysis.NativeC2InteriorEstimate

/-! Uniform actual gradient control on precompact regions at C²
regularity. The actual Laplacian is the source; no equation is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.NirenbergEuclidean

theorem exists_uniform_C2_local_gradient_estimate
    {O W V : Set E} (hO : IsOpen O) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWO : closure W ⊆ O) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVW : closure V ⊆ W) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ u : E → ℝ,ContDiffOn ℝ 2 u O →
      (∫ x in V,∑ j : Fin 3,nativeCoordinateFirst j u x^2) ≤
        G*((∫ x in W,u x^2)+(∫ x in W,nativeCoordinateLaplacian u x^2)) := by
  obtain ⟨η,hη,hηc,hηrange,hηone,hηW,N,hN,hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hVc hW hVW
  refine ⟨1+4*3*N^2,by positivity,?_⟩
  intro u hu
  obtain ⟨v,hv,hvc,hvu⟩ := exists_finite_compact_extension_near_compact 2 hO hWc hWO hu
  have hd := nativeCoordinateC2_compact_data hv hvc
  have hDη' : ∀ x (j : Fin 3),|fderiv ℝ η x (EuclideanSpace.single j 1)| ≤ N := by
    intro x j
    have h := (fderiv ℝ η x).le_opNorm (EuclideanSpace.single j 1)
    simp only [PiLp.norm_single,norm_one,mul_one,Real.norm_eq_abs] at h
    exact h.trans (hDη x)
  have hgrad := native_C1_gradient_integral_le hW hV.measurableSet (subset_closure.trans hVW)
    hη hηc hηW (fun x => hηrange (mem_range_self x))
    (fun x hx => hηone x (subset_closure hx)) hN hDη'
    (hv.of_le (by norm_num)).contDiffOn (hd.1.restrict W) (hd.2.2.1.restrict W)
    (fun j => (hd.2.1 j).restrict W) (nativeCoordinateLaplacian_weakEquation hW hv)
  simp only [neg_sq] at hgrad
  have heV : (fun x => ∑ j : Fin 3,nativeCoordinateFirst j v x^2)
      =ᵐ[volume.restrict V] (fun x => ∑ j : Fin 3,nativeCoordinateFirst j u x^2) := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    apply Finset.sum_congr rfl
    intro j _
    rw [(nativeCoordinateFirst_congr_germ
      (hvu x (subset_closure (hVW (subset_closure hx)))) j).self_of_nhds]
  have he0 : (fun x => v x^2) =ᵐ[volume.restrict W] (fun x => u x^2) := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
    rw [(hvu x (subset_closure hx)).self_of_nhds]
  have he2 : (fun x => nativeCoordinateLaplacian v x^2) =ᵐ[volume.restrict W]
      (fun x => nativeCoordinateLaplacian u x^2) := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
    rw [nativeCoordinateLaplacian_congr_germ (hvu x (subset_closure hx))]
  change (∫ x in V,∑ j : Fin 3,nativeCoordinateFirst j v x^2) ≤ _ at hgrad
  rwa [integral_congr_ae heV,integral_congr_ae he0,integral_congr_ae he2] at hgrad

#print axioms exists_uniform_C2_local_gradient_estimate
end Yamabe3.Analysis.SpherePolar
