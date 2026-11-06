import Yamabe3.Analysis.L2BoundedScalarMultiplier

/-! Zero extension of the actual restricted L2 class, with exact norm.
The construction does not choose an independent representative on the domain. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Yamabe3.Analysis
variable {X:Type*} [MeasurableSpace X] {μ:Measure X} (O:Set X) (hO:MeasurableSet O)

def l2ZeroExtend (U:Lp ℝ 2 (μ.restrict O)) : Lp ℝ 2 μ :=
  ((memLp_indicator_iff_restrict hO).mpr (Lp.memLp U)).toLp (O.indicator (U:X→ℝ))

theorem l2ZeroExtend_ae (U:Lp ℝ 2 (μ.restrict O)) :
    (l2ZeroExtend O hO U:X→ℝ)=ᵐ[μ] O.indicator (U:X→ℝ) :=
  ((memLp_indicator_iff_restrict hO).mpr (Lp.memLp U)).coeFn_toLp

theorem l2ZeroExtend_norm (U:Lp ℝ 2 (μ.restrict O)) : ‖l2ZeroExtend O hO U‖=‖U‖ := by
  rw [l2ZeroExtend,Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict hO,Lp.norm_def]

def l2ZeroExtendCLM : Lp ℝ 2 (μ.restrict O) →L[ℝ] Lp ℝ 2 μ :=
  ({toFun:=l2ZeroExtend O hO
    map_add':=by
      intro U V
      apply Lp.ext
      have hsum:O.indicator ((U+V:Lp ℝ 2 (μ.restrict O)):X→ℝ)=ᵐ[μ]
          O.indicator (fun x=>U x+V x) :=
        (ae_eq_restrict_iff_indicator_ae_eq hO).mp (Lp.coeFn_add U V)
      filter_upwards [l2ZeroExtend_ae O hO (U+V),l2ZeroExtend_ae O hO U,l2ZeroExtend_ae O hO V,
        Lp.coeFn_add (l2ZeroExtend O hO U) (l2ZeroExtend O hO V),hsum] with x hs hu hv ha hi
      rw [hs,hi,ha]
      simp only [Pi.add_apply,hu,hv,indicator_add]
    map_smul':=by
      intro c U
      simp only [RingHom.id_apply]
      apply Lp.ext
      have hsm:O.indicator ((c • U:Lp ℝ 2 (μ.restrict O)):X→ℝ)=ᵐ[μ]
          O.indicator (fun x=>c*U x) :=
        (ae_eq_restrict_iff_indicator_ae_eq hO).mp (Lp.coeFn_smul c U)
      filter_upwards [l2ZeroExtend_ae O hO (c • U),l2ZeroExtend_ae O hO U,
        Lp.coeFn_smul c (l2ZeroExtend O hO U),hsm] with x hs hu ha hi
      rw [hs,hi,ha]
      simp only [Pi.smul_apply,smul_eq_mul,hu,indicator_const_mul]
    }:Lp ℝ 2 (μ.restrict O) →ₗ[ℝ] Lp ℝ 2 μ).mkContinuous 1
      (fun U=>by
        change ‖l2ZeroExtend O hO U‖ ≤ 1*‖U‖
        rw [l2ZeroExtend_norm,one_mul])

theorem l2ZeroExtendCLM_norm : ‖l2ZeroExtendCLM (μ:=μ) O hO‖ ≤ 1 :=
  (l2ZeroExtendCLM O hO).opNorm_le_bound zero_le_one (fun U=>by rw [show l2ZeroExtendCLM O hO U=l2ZeroExtend O hO U from rfl,l2ZeroExtend_norm,one_mul])

#print axioms l2ZeroExtend_ae
#print axioms l2ZeroExtend_norm
#print axioms l2ZeroExtendCLM_norm
end Yamabe3.Analysis
