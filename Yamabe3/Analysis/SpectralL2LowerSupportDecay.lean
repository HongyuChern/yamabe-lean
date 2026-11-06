import Yamabe3.Analysis.SpectralL2ExponentialMoment
import Yamabe3.Analysis.L2RealPairingBound

/-! A lower time support bound for an L2 source gives an actual
exponential estimate for its full-line free resolvent. The constant is
chosen before the source; no pointwise source bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

def spectralLowerWeight (a b : ℝ) : ℝ→ℝ := (Ici b).indicator (fun s => Real.exp (-a*s))

theorem spectralLowerWeight_memLp {a : ℝ} (ha : 0<a) (b : ℝ) :
    MemLp (spectralLowerWeight a b) 2 := by
  apply (memLp_two_iff_integrable_sq
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.indicator measurableSet_Ici).aestronglyMeasurable)).mpr
  have hi : IntegrableOn (fun s : ℝ => Real.exp ((-2*a)*s)) (Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi (by linarith) b)
  have he : (fun s => spectralLowerWeight a b s^2)=(Ici b).indicator (fun s : ℝ => Real.exp ((-2*a)*s)) := by
    funext s
    by_cases hs : s∈Ici b
    · simp only [spectralLowerWeight,indicator_of_mem hs,←Real.exp_nat_mul]
      congr 1
      ring
    · simp only [spectralLowerWeight,indicator_of_notMem hs,zero_pow (by decide : 2≠0)]
  change Integrable (fun s => spectralLowerWeight a b s^2)
  rw [he]
  exact hi.integrable_indicator measurableSet_Ici

theorem spectralMajorant_exp_upper {k δ a : ℝ} (hk : 0<k) (ha : |δ+a|≤k) (r : ℝ) :
    spectralMajorant k δ r≤Real.exp (a*r)/(2*k) := by
  apply (div_le_div_iff_of_pos_right (by positivity : 0<2*k)).mpr
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right ha (abs_nonneg r)
  have hmul := neg_abs_le ((δ+a)*r)
  rw [abs_mul] at hmul
  nlinarith only [h,hmul]

theorem exists_spectralL2_lower_support_decay {ι : Type*} (k : ι→ℝ) {k₀ δ a : ℝ}
    (hk₀ : 0<k₀) (hk : ∀i,k₀≤k i) (hδ : |δ|<k₀) (ha : 0<a) (hshift : |δ+a|≤k₀)
    (b : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ),
      (∀ᵐs : ℝ ∂volume,s<b → F s=0) → ∀t : ℝ,
      ‖spectralL2Convolution k hk₀ hk δ F t‖≤C*‖F‖*Real.exp (a*t) := by
  let W := spectralLowerWeight a b
  have hW := spectralLowerWeight_memLp ha b
  refine ⟨(eLpNorm W 2).toReal/(2*k₀),by positivity,fun F hF t => ?_⟩
  have hm := hW.integrable_mul (Lp.memLp F).norm
  have hi := hm.const_mul (Real.exp (a*t)/(2*k₀))
  have hb : ∀ᵐs : ℝ ∂volume,‖weightedSpectralKernel k hk₀ hk δ (t-s) (F s)‖≤
      (Real.exp (a*t)/(2*k₀))*(W s*‖F s‖) := by
    filter_upwards [hF] with s hs
    by_cases hsb : b≤s
    · have he : spectralMajorant k₀ δ (t-s)≤(Real.exp (a*t)/(2*k₀))*W s := by
        apply (spectralMajorant_exp_upper hk₀ hshift (t-s)).trans_eq
        dsimp only [W,spectralLowerWeight]
        rw [indicator_of_mem (show s∈Ici b from hsb)]
        rw [show a*(t-s)=a*t+-a*s by ring,Real.exp_add]
        ring
      exact (((weightedSpectralKernel k hk₀ hk δ (t-s)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (weightedSpectralKernel_norm_le k hk₀ hk δ (t-s)) (norm_nonneg _))).trans
        ((mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (by ring))
    · rw [hs (lt_of_not_ge hsb),map_zero,norm_zero,mul_zero,mul_zero]
  have hn := norm_integral_le_of_norm_le hi hb
  change ‖spectralL2Convolution k hk₀ hk δ F t‖≤_ at hn
  rw [integral_const_mul] at hn
  have hh := integral_mul_le_eLpNorm_two volume hW (Lp.memLp F).norm
  rw [eLpNorm_norm,←Lp.norm_def] at hh
  apply hn.trans
  exact (mul_le_mul_of_nonneg_left hh (by positivity : 0≤Real.exp (a*t)/(2*k₀))).trans_eq (by ring)

#print axioms spectralLowerWeight_memLp
#print axioms spectralMajorant_exp_upper
#print axioms exists_spectralL2_lower_support_decay
end Yamabe3.Analysis.Delaunay
