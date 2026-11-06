import Yamabe3.Analysis.L2ContinuousSourceDense
import Mathlib.Analysis.Normed.Operator.Extend

/-! The actual bounded continuous L2 sources form a linear source space
with dense linear inclusion into L2. The extension API preserves actual
source classes and does not install an additional regularity assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis

variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]

def continuousL2Source : Submodule ℝ (ℝ →ᵇ H) where
  carrier := {F | MemLp (F : ℝ → H) 2 (volume : Measure ℝ)}
  zero_mem' := MemLp.zero
  add_mem' := by intro F G hF hG;exact hF.add hG
  smul_mem' := by intro c F hF;exact hF.const_smul c

def continuousL2SourceInclusion : continuousL2Source H →ₗ[ℝ] Lp H 2 (volume : Measure ℝ) where
  toFun F := F.property.toLp F.val
  map_add' F G := MemLp.toLp_add F.property G.property
  map_smul' c F := MemLp.toLp_const_smul c F.property

theorem continuousL2SourceInclusion_dense : DenseRange (continuousL2SourceInclusion H) := by
  apply (Lp.boundedContinuousFunction_dense H volume (by norm_num : (2:ℝ≥0∞)≠⊤)).mono
  intro Z hZ
  obtain ⟨F,hF⟩ := Lp.mem_boundedContinuousFunction_iff.mp hZ
  have hae : (Z : ℝ → H)=ᵐ[volume] F := by
    change ((Z : ℝ →ₘ[volume] H) : ℝ → H)=ᵐ[volume] F
    rw [←hF]
    exact F.toContinuousMap.coeFn_toAEEqFun volume
  have hF2 : MemLp (F : ℝ → H) 2 := (Lp.memLp Z).ae_eq hae
  refine ⟨⟨F,hF2⟩,?_⟩
  apply Lp.ext
  exact hF2.coeFn_toLp.trans hae.symm

theorem continuousL2SourceInclusion_injective : Function.Injective (continuousL2SourceInclusion H) := by
  intro F G he
  have hae : (F.val : ℝ → H)=ᵐ[volume] G.val := by
    exact F.property.coeFn_toLp.symm.trans ((Lp.ext_iff.mp he).trans G.property.coeFn_toLp)
  have hp := Measure.eq_of_ae_eq hae F.val.continuous G.val.continuous
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro t
  exact congrFun hp t

#print axioms continuousL2SourceInclusion
#print axioms continuousL2SourceInclusion_dense
#print axioms continuousL2SourceInclusion_injective
end Yamabe3.Analysis
