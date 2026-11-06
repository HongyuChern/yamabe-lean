import Yamabe3.Analysis.SpectralL2FreeCLM

/-! Multiplication by the same bounded potential on the actual L2
quotient. This supplies a bounded linear operation, not a claim that the
weighted potential-resolvent composition is a contraction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2Potential_mul_memLp {ι : Type*} (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    MemLp (fun t => V t • F t) 2 := by
  apply ((Lp.memLp F).const_smul ‖V‖).mono
    (V.continuous.aestronglyMeasurable.smul (Lp.memLp F).1)
  exact Eventually.of_forall fun t => by
    change ‖V t • F t‖ ≤ ‖‖V‖ • F t‖
    simpa only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_norm] using
      mul_le_mul_of_nonneg_right (V.norm_coe_le_norm t) (norm_nonneg (F t))

def spectralL2PotentialMul {ι : Type*} (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) : Lp (SpectralSpace ι) 2 (volume : Measure ℝ) :=
  (spectralL2Potential_mul_memLp V F).toLp (fun t => V t • F t)

theorem spectralL2PotentialMul_coe_ae {ι : Type*} (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    (spectralL2PotentialMul V F : ℝ → SpectralSpace ι)=ᵐ[volume](fun t => V t • F t) :=
  (spectralL2Potential_mul_memLp V F).coeFn_toLp

theorem spectralL2PotentialMul_norm_le {ι : Type*} (V : ℝ →ᵇ ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    ‖spectralL2PotentialMul V F‖ ≤ ‖V‖*‖F‖ := by
  have hb : eLpNorm (fun t => V t • F t) 2 ≤ eLpNorm (‖V‖ • (F : ℝ → SpectralSpace ι)) 2 := by
    apply eLpNorm_mono_ae
    exact Eventually.of_forall fun t => by
      simpa only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_norm] using
        mul_le_mul_of_nonneg_right (V.norm_coe_le_norm t) (norm_nonneg (F t))
  rw [eLpNorm_const_smul] at hb
  have ht : ‖‖V‖‖ₑ*eLpNorm (F : ℝ → SpectralSpace ι) 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (Lp.memLp F).2.ne
  have hr := ENNReal.toReal_mono ht hb
  unfold spectralL2PotentialMul
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul,enorm_norm,toReal_enorm,Lp.norm_def] using hr

theorem spectralL2PotentialMul_add {ι : Type*} (V : ℝ →ᵇ ℝ)
    (F G : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2PotentialMul V (F+G)=spectralL2PotentialMul V F+spectralL2PotentialMul V G := by
  apply Lp.ext
  filter_upwards [spectralL2PotentialMul_coe_ae V (F+G),spectralL2PotentialMul_coe_ae V F,
    spectralL2PotentialMul_coe_ae V G,Lp.coeFn_add F G,
    Lp.coeFn_add (spectralL2PotentialMul V F) (spectralL2PotentialMul V G)] with t hs hf hg hfg ho
  simpa only [Pi.add_apply,hs,hf,hg,hfg,ho] using smul_add (V t) (F t) (G t)

theorem spectralL2PotentialMul_smul {ι : Type*} (V : ℝ →ᵇ ℝ) (c : ℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) :
    spectralL2PotentialMul V (c • F)=c • spectralL2PotentialMul V F := by
  apply Lp.ext
  filter_upwards [spectralL2PotentialMul_coe_ae V (c • F),spectralL2PotentialMul_coe_ae V F,
    Lp.coeFn_smul c F,Lp.coeFn_smul c (spectralL2PotentialMul V F)] with t hs hf hcf ho
  simpa only [Pi.smul_apply,hs,hf,hcf,ho] using smul_comm (V t) c (F t)

def spectralL2PotentialMulCLM {ι : Type*} (V : ℝ →ᵇ ℝ) :
    Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →L[ℝ] Lp (SpectralSpace ι) 2 (volume : Measure ℝ) :=
  ({toFun := spectralL2PotentialMul V
    map_add' := spectralL2PotentialMul_add V
    map_smul' := spectralL2PotentialMul_smul V} :
      Lp (SpectralSpace ι) 2 (volume : Measure ℝ) →ₗ[ℝ] Lp (SpectralSpace ι) 2 (volume : Measure ℝ)).mkContinuous
    ‖V‖ (spectralL2PotentialMul_norm_le V)

#print axioms spectralL2PotentialMul_norm_le
#print axioms spectralL2PotentialMul_add
#print axioms spectralL2PotentialMul_smul
end Yamabe3.Analysis.Delaunay
