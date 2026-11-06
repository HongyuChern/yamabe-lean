import Yamabe3.Analysis.NativeC1CollarTraceBound

/-! Actual radial derivative restrictions are controlled by actual
first and second volume derivatives. No trace operator is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

theorem native_continuous_sphere_memLp {f : S → ℝ} (hf : Continuous f) :
    MemLp f 2 angularVolume := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  simpa only [integrableOn_univ,Pi.pow_apply] using!
    (hf.pow 2).continuousOn.integrableOn_compact (μ := angularVolume)
      (isCompact_univ : IsCompact (univ : Set S))

theorem native_C1_sphere_restriction_memLp {u : E → ℝ}
    (hu : ContinuousOn u ({0}ᶜ : Set E)) : MemLp (fun θ : S => u (θ:E)) 2 angularVolume := by
  apply native_continuous_sphere_memLp
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hx : (θ:E) ≠ 0 := by
    intro h
    have hn := norm_eq_of_mem_sphere θ
    rw [h,norm_zero] at hn
    norm_num at hn
  exact (hu.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds hx)).comp continuous_subtype_val.continuousAt

theorem exists_native_C2_collar_normal_trace_bound :
    ∃ C : ℝ,0 ≤ C ∧ ∀ u : E → ℝ,ContDiffOn ℝ 2 u ({0}ᶜ : Set E) →
      (∫ θ : S,(fderiv ℝ u (θ:E) (θ:E))^2 ∂angularVolume) ≤
        C*(∑ j : Fin 3,∫ x in nativePoissonEntranceCollar,
          nativeCoordinateFirst j u x^2+∑ k : Fin 3,nativeCoordinateSecond k j u x^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_native_C1_collar_value_trace_bound
  refine ⟨C,hC,fun u hu => ?_⟩
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hp (j : Fin 3) : ContDiffOn ℝ 1 (nativeCoordinateFirst j u) {0}ᶜ :=
    (hu.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  have hpr (j : Fin 3) := native_C1_sphere_restriction_memLp (hp j).continuousOn
  have hnr : Continuous (fun θ : S => fderiv ℝ u (θ:E) (θ:E)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hx : (θ:E) ≠ 0 := by
      intro h
      have hn := norm_eq_of_mem_sphere θ
      rw [h,norm_zero] at hn
      norm_num at hn
    exact ((hu.continuousOn_fderiv_of_isOpen hO (by norm_num)).continuousAt (hO.mem_nhds hx) |>.comp
      continuous_subtype_val.continuousAt).clm_apply continuous_subtype_val.continuousAt
  have hpoint (θ : S) : (fderiv ℝ u (θ:E) (θ:E))^2 ≤ ∑ j : Fin 3,nativeCoordinateFirst j u (θ:E)^2 := by
    have h := (fderiv ℝ u (θ:E)).le_opNorm (θ:E)
    rw [norm_eq_of_mem_sphere θ,mul_one,Real.norm_eq_abs] at h
    have hh := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
    simpa only [sq_abs,native_fderiv_norm_sq_eq_partials] using hh
  have hle := integral_mono (native_continuous_sphere_memLp hnr).integrable_sq
    (integrable_finsetSum _ (fun j _ => (hpr j).integrable_sq)) hpoint
  rw [integral_finsetSum _ (fun j _ => (hpr j).integrable_sq)] at hle
  apply hle.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact hbound (nativeCoordinateFirst j u) (hp j)

#print axioms native_C1_sphere_restriction_memLp
#print axioms exists_native_C2_collar_normal_trace_bound
end Yamabe3.Analysis.SpherePolar
