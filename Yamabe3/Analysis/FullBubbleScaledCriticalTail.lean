import Yamabe3.Analysis.FullBubbleCriticalTail
import Yamabe3.Analysis.CriticalPotentialDilation

/-! Actual factor-eight bubble-tail reactions. A large dimensionless
tail radius makes their L6 -> L^(6/5) multiplier norm small, uniformly
in the independent physical entrance scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

def fullBubbleScaledTail (τ s t : ℝ) (x : E) : ℝ :=
  Real.exp (-2*t)*fullBubblePotentialTail τ (Real.exp s) (Real.exp (-t) • x)

private instance scaledTailHolder : ENNReal.HolderTriple (3/2) 6 (6/5) := by
  constructor
  have h32 : (3/2 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  have h65 : (6/5 : ℝ≥0∞) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.add_ne_top.mpr ⟨ENNReal.inv_ne_top.mpr h32, by norm_num⟩)
    (ENNReal.inv_ne_top.mpr h65)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

theorem fullBubbleScaledTail_reaction_bound (τ s t : ℝ) (u : E → ℝ) (hu : MemLp u 6 volume) :
    MemLp (fun x : E => 8*(fullBubbleScaledTail τ s t x*u x)) (6/5 : ℝ≥0∞) volume ∧
      eLpNorm (fun x : E => 8*(fullBubbleScaledTail τ s t x*u x)) (6/5 : ℝ≥0∞) volume ≤
        ((ENNReal.ofReal (120*Real.exp (2*τ))*eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume)*
          ENNReal.ofReal (Real.exp (-2*s)))*eLpNorm u 6 volume := by
  have hq := memLp_exp_potential_dilation t _ (fullBubblePotentialTail_memLp τ s)
  change MemLp (fullBubbleScaledTail τ s t) (3/2 : ℝ≥0∞) volume at hq
  have hn : eLpNorm (fullBubbleScaledTail τ s t) (3/2 : ℝ≥0∞) volume ≤
      (ENNReal.ofReal (15*Real.exp (2*τ))*eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume)*
        ENNReal.ofReal (Real.exp (-2*s)) := by
    rw [show fullBubbleScaledTail τ s t = fun x => Real.exp (-2*t)*fullBubblePotentialTail τ (Real.exp s) (Real.exp (-t) • x) from rfl,
      eLpNorm_exp_potential_dilation]
    exact fullBubblePotentialTail_critical_norm τ s
  have hp : MemLp (fun x : E => fullBubbleScaledTail τ s t x*u x) (6/5 : ℝ≥0∞) volume := hu.mul' hq
  refine ⟨hp.const_mul 8, ?_⟩
  change eLpNorm ((8 : ℝ) • (fun x : E => fullBubbleScaledTail τ s t x*u x)) _ _ ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 8)]
  have hh := (eLpNorm_smul_le_mul_eLpNorm (p := (3/2 : ℝ≥0∞)) (q := 6) (r := (6/5 : ℝ≥0∞)) hu.1 hq.1).trans
    (mul_le_mul hn le_rfl zero_le zero_le)
  apply (mul_le_mul le_rfl hh zero_le zero_le).trans_eq
  have hc : ENNReal.ofReal (8 : ℝ)*ENNReal.ofReal (15*Real.exp (2*τ)) =
      ENNReal.ofReal (120*Real.exp (2*τ)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
    congr 1
    ring
  calc
    _ = ((ENNReal.ofReal (8 : ℝ)*ENNReal.ofReal (15*Real.exp (2*τ)))*
      eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume*ENNReal.ofReal (Real.exp (-2*s)))*eLpNorm u 6 volume := by ring
    _ = _ := by rw [hc]

theorem exists_fullBubbleScaledTail_small_reaction (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃s : ℝ, 0 ≤ s ∧ ∀t : ℝ, ∀u : E → ℝ, MemLp u 6 volume →
      MemLp (fun x : E => 8*(fullBubbleScaledTail τ s t x*u x)) (6/5 : ℝ≥0∞) volume ∧
        eLpNorm (fun x : E => 8*(fullBubbleScaledTail τ s t x*u x)) (6/5 : ℝ≥0∞) volume ≤
          ENNReal.ofReal ε*eLpNorm u 6 volume := by
  let c := ENNReal.ofReal (120*Real.exp (2*τ))*eLpNorm (exteriorInverseFourth 1) (3/2 : ℝ≥0∞) volume
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top exteriorInverseFourth_memLp_one.eLpNorm_lt_top.ne
  have he : Tendsto (fun s : ℝ => Real.exp (-2*s)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
    simpa only [Function.comp_def, neg_mul, id_eq] using hh
  have hh : ∀ᶠs : ℝ in atTop, c.toReal*Real.exp (-2*s) < ε := by
    have hl : Tendsto (fun s : ℝ => c.toReal*Real.exp (-2*s)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul he
    exact hl.eventually (gt_mem_nhds hε)
  obtain ⟨s,hs,hsb⟩ := ((eventually_ge_atTop (0 : ℝ)).and hh).exists
  refine ⟨s,hs,fun t u hu => ?_⟩
  have hb : c*ENNReal.ofReal (Real.exp (-2*s)) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hct, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hsb.le
  have hx := fullBubbleScaledTail_reaction_bound τ s t u hu
  exact ⟨hx.1, hx.2.trans (mul_le_mul hb le_rfl zero_le zero_le)⟩

#print axioms fullBubbleScaledTail_reaction_bound
#print axioms exists_fullBubbleScaledTail_small_reaction
end Yamabe3.Analysis.SpherePolar
