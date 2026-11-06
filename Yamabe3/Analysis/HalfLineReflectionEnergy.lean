import Yamabe3.Analysis.HalfLineFiniteReflection
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! A quantitative L² extension bound for the actual reflection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology
namespace Yamabe3.Analysis.Delaunay
variable {ι : Type*} [Fintype ι]

theorem halfLineReflection_square_integral
    (r c : ι → ℝ) (hr : ∀ j, 0 < r j) (hc : ∑ j,c j = 1)
    {f : ℝ → ℝ} (hfc : ContinuousOn f (Ici 0))
    (hf : IntegrableOn (fun t => f t^2) (Ioi 0)) :
    Integrable (fun t => halfLineReflection r c f t^2) ∧
      (∫ t : ℝ, halfLineReflection r c f t^2) ≤
        (1+(∑ j,c j^2)*(∑ j,(r j)⁻¹))*(∫ t : ℝ in Ioi 0, f t^2) := by
  classical
  have hscale (j : ι) : IntegrableOn (fun t => f (r j*t)^2) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun t => f t^2) 0 (hr j)).mpr
    simpa only [mul_zero] using hf
  have hneg (j : ι) : IntegrableOn (fun t => f (-r j*t)^2) (Iic 0) := by
    apply (integrableOn_Iic_iff_integrableOn_Iio).mpr
    have hh : IntegrableOn (fun t => f (r j*t)^2) (Ioi (-(0:ℝ))) := by
      simpa only [neg_zero] using hscale j
    simpa only [neg_zero,mul_neg,neg_mul] using hh.comp_neg_Iio
  have hi (j : ι) : (∫ t : ℝ in Iic 0, f (-r j*t)^2) =
      (r j)⁻¹*(∫ t : ℝ in Ioi 0, f t^2) := by
    have h := integral_comp_neg_Iic 0 (fun t => f (r j*t)^2)
    simp only [mul_neg,neg_mul,neg_zero] at h
    simp only [neg_mul]
    rw [h,integral_comp_mul_left_Ioi (fun t => f t^2) 0 (hr j)]
    simp only [mul_zero,smul_eq_mul]
  have hleft_eq (t : ℝ) (ht : t ≤ 0) :
      halfLineReflection r c f t = ∑ j,c j*f (-r j*t) := by
    rcases lt_or_eq_of_le ht with ht | rfl
    · exact if_neg (not_le.mpr ht)
    · simp only [halfLineReflection,le_refl,if_true,mul_zero,← Finset.sum_mul,hc,one_mul]
  have hbound (t : ℝ) (ht : t ≤ 0) :
      halfLineReflection r c f t^2 ≤ (∑ j,c j^2)*(∑ j,f (-r j*t)^2) := by
    rw [hleft_eq t ht]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (fun j => f (-r j*t))
  have hb := (integrable_finsetSum Finset.univ (fun j _ => hneg j)).const_mul (∑ j,c j^2)
  have hleft : IntegrableOn (fun t => halfLineReflection r c f t^2) (Iic 0) := by
    apply hb.mono' ((halfLineReflection_continuous r c hr hc hfc).pow 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    simp only [Pi.pow_apply]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hbound t ht
  have hright_eq : (fun t => halfLineReflection r c f t^2)
      =ᵐ[volume.restrict (Ioi 0)] (fun t => f t^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [halfLineReflection_eq_nonneg r c f ht.le]
  have hright := hf.congr hright_eq.symm
  have hall : Integrable (fun t => halfLineReflection r c f t^2) := by
    have h := hleft.union hright
    rwa [Iic_union_Ioi,integrableOn_univ] at h
  refine ⟨hall,?_⟩
  have hle := integral_mono_ae hleft hb (by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    exact hbound t ht)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hneg j)] at hle
  simp_rw [hi] at hle
  rw [← Finset.sum_mul] at hle
  have he : (∫ t : ℝ, halfLineReflection r c f t^2) =
      (∫ t : ℝ in Iic 0, halfLineReflection r c f t^2)+
        (∫ t : ℝ in Ioi 0, f t^2) := by
    rw [← integral_congr_ae hright_eq,
      ← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hleft hright,
      Iic_union_Ioi,Measure.restrict_univ]
  rw [he]
  nlinarith only [hle]

#print axioms halfLineReflection_square_integral
end Yamabe3.Analysis.Delaunay
