import Yamabe3.Analysis.SpectralL2OriginalIdentification
import Mathlib.MeasureTheory.Function.L2Space

/-! Finite L2 norm and local translation domination of the actual sharp
spectral majorant. These estimates make entrance evaluation legitimate
for L2 sources without assigning arbitrary values to an L2 class. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp
namespace Yamabe3.Analysis.Delaunay

theorem spectralMajorant_memLp_two {k₀ δ : ℝ} (hk₀ : 0<k₀) (hδ : |δ|<k₀) :
    MemLp (spectralMajorant k₀ δ) 2 := by
  have hc : Continuous (spectralMajorant k₀ δ) := by unfold spectralMajorant;fun_prop
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have h2 : |2*δ|<2*k₀ := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)];linarith
  have he : (fun t => spectralMajorant k₀ δ t^2)=fun t => spectralMajorant (2*k₀) (2*δ) t/k₀ := by
    funext t
    unfold spectralMajorant
    rw [div_pow,←Real.exp_nat_mul]
    have hex : (2:ℝ)*(-δ*t-k₀*|t|)=-(2*δ)*t-(2*k₀)*|t| := by ring
    simp only [Nat.cast_ofNat,hex]
    field_simp <;> ring
  rw [he]
  exact (spectralMajorant_integral (by linarith) h2).1.div_const k₀

theorem spectralMajorant_translate_le {k₀ δ : ℝ} (hk₀ : 0<k₀) (t t₀ s : ℝ) :
    spectralMajorant k₀ δ (t-s) ≤
      Real.exp ((|δ|+k₀)*|t-t₀|)*spectralMajorant k₀ δ (t₀-s) := by
  unfold spectralMajorant
  rw [←mul_div_assoc,←Real.exp_add]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hd : -δ*(t-t₀) ≤ |δ| * |t-t₀| := by
    simpa only [abs_mul,abs_neg] using (le_abs_self (-δ*(t-t₀)))
  have ha : |t₀-s| ≤ |t-t₀|+|t-s| := by
    have h := abs_sub_le t₀ t s
    simpa only [abs_sub_comm t₀ t] using h
  nlinarith

theorem spectralMajorant_translate_memLp {k₀ δ : ℝ} (hk₀ : 0<k₀) (hδ : |δ|<k₀) (t : ℝ) :
    MemLp (fun s => spectralMajorant k₀ δ (t-s)) 2 :=
  (spectralMajorant_memLp_two hk₀ hδ).comp_measurePreserving (volume.measurePreserving_sub_left t)

#print axioms spectralMajorant_memLp_two
#print axioms spectralMajorant_translate_le
#print axioms spectralMajorant_translate_memLp
end Yamabe3.Analysis.Delaunay
