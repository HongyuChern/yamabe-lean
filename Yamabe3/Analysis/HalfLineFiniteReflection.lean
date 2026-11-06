import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Piecewise
import Mathlib.Tactic

/-! Actual finite reflection across a half-line entrance. Matching
moments, not invented boundary derivatives, give a genuine two-sided
derivative of the same positive-time field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay
variable {ι : Type*} [Fintype ι]

def halfLineReflection (r c : ι → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then f t else ∑ j, c j*f (-r j*t)

theorem halfLineReflection_eq_nonneg (r c : ι → ℝ) (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    halfLineReflection r c f t = f t := if_pos ht

theorem halfLineReflection_continuous
    (r c : ι → ℝ) (hr : ∀ j, 0 < r j) (hc : ∑ j,c j = 1)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) :
    Continuous (halfLineReflection r c f) := by
  apply continuous_if
  · intro t ht
    have ht0 : t = 0 := by
      change t ∈ frontier (Ici (0:ℝ)) at ht
      simpa only [frontier_Ici, mem_singleton_iff] using ht
    subst t
    simp only [mul_zero, ← Finset.sum_mul, hc, one_mul]
  · change ContinuousOn f (closure (Ici (0:ℝ)))
    rwa [isClosed_Ici.closure_eq]
  · have hneg : ContinuousOn (fun t : ℝ => ∑ j,c j*f (-r j*t)) (Iic 0) := by
      apply continuousOn_finsetSum
      intro j _
      apply ContinuousOn.const_mul
      exact hf.comp (continuous_const.mul continuous_id).continuousOn
        (fun t ht => mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hr j).le) ht)
    simp only [not_le]
    change ContinuousOn (fun t : ℝ => ∑ j,c j*f (-r j*t)) (closure (Iio (0:ℝ)))
    rwa [closure_Iio]

theorem halfLineReflection_hasDeriv
    (r c : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hc : ∑ j,c j = 1) (hcd : ∑ j, -r j*c j = 1)
    {f df : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (df t) (Ici 0) t)
    (t : ℝ) :
    HasDerivAt (halfLineReflection r c f)
      (halfLineReflection r (fun j => -r j*c j) df t) t := by
  classical
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hsum : HasDerivAt (fun s : ℝ => ∑ j,c j*f (-r j*s))
        (∑ j,(-r j*c j)*df (-r j*t)) t := by
      apply HasDerivAt.fun_sum
      intro j _
      have hx : 0 < -r j*t := mul_pos_of_neg_of_neg (neg_neg_of_pos (hr j)) ht
      have h := (((hf (-r j*t) hx.le).hasDerivAt (Ici_mem_nhds hx)).comp t
        ((hasDerivAt_id t).const_mul (-r j))).const_mul (c j)
      apply h.congr_deriv
      ring
    have he : halfLineReflection r c f =ᶠ[𝓝 t] fun s => ∑ j,c j*f (-r j*s) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact if_neg (not_le.mpr hs)
    simpa only [halfLineReflection, if_neg (not_le.mpr ht)] using hsum.congr_of_eventuallyEq he
  · have hrgt : HasDerivWithinAt (halfLineReflection r c f) (df 0) (Ici 0) 0 :=
      (hf 0 le_rfl).congr_of_mem (fun s hs => halfLineReflection_eq_nonneg r c f hs) (mem_Ici.mpr le_rfl)
    have hsum : HasDerivWithinAt (fun s : ℝ => ∑ j,c j*f (-r j*s))
        (∑ j,(-r j*c j)*df 0) (Iic 0) 0 := by
      apply HasDerivWithinAt.fun_sum
      intro j _
      have hmap : MapsTo (fun s : ℝ => -r j*s) (Iic 0) (Ici 0) :=
        fun s hs => mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hr j).le) hs
      have h := ((hf (-r j*0) (by simp)).comp 0
        ((hasDerivAt_id (0:ℝ)).const_mul (-r j)).hasDerivWithinAt hmap).const_mul (c j)
      apply h.congr_deriv
      simp only [mul_zero]
      ring
    rw [← Finset.sum_mul,hcd,one_mul] at hsum
    have hlft : HasDerivWithinAt (halfLineReflection r c f) (df 0) (Iic 0) 0 := by
      apply hsum.congr_of_mem _ (mem_Iic.mpr le_rfl)
      intro s hs
      rcases lt_or_eq_of_le (mem_Iic.mp hs) with hs | rfl
      · exact if_neg (not_le.mpr hs)
      · simp only [halfLineReflection, le_refl, if_true, mul_zero, ← Finset.sum_mul, hc, one_mul]
    have h := (hrgt.union hlft).hasDerivAt (by
      rw [union_comm, Iic_union_Ici]
      exact univ_mem)
    simpa only [halfLineReflection_eq_nonneg r (fun j => -r j*c j) df (le_refl 0)] using h
  · have he : halfLineReflection r c f =ᶠ[𝓝 t] f := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact if_pos hs.le
    simpa only [halfLineReflection, if_pos ht.le] using
      ((hf t ht.le).hasDerivAt (Ici_mem_nhds ht)).congr_of_eventuallyEq he

#print axioms halfLineReflection_continuous
#print axioms halfLineReflection_hasDeriv
end Yamabe3.Analysis.Delaunay
