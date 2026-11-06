import Yamabe3.Analysis.NativeCollarJetSpace
import Yamabe3.Analysis.L2BoundedScalarMultiplier

/-! Actual continuous coefficients act on the collar L2 space. The
operator is independent of the auxiliary compactness bound, and obeys
any subsequently proved pointwise bound on the same collar. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology
namespace Yamabe3.Analysis.SpherePolar

private theorem nativeCollar_coefficient_bounded (q : E → ℝ) (hq : Continuous q) :
    ∃ C : ℝ,0≤C ∧ ∀ x ∈ nativePoissonEntranceCollar,‖q x‖≤C := by
  obtain ⟨C,hC⟩ := (nativePolarTimeWindow_precompact (1/2)).exists_bound_of_continuousOn hq.continuousOn
  exact ⟨max C 0,le_max_right _ _,fun x hx => (hC x (subset_closure hx)).trans (le_max_left _ _)⟩

def nativeCollarScalarMulCLM (q : E → ℝ) (hq : Continuous q) : NativeCollarL2 →L[ℝ] NativeCollarL2 :=
  l2ScalarMulCLM q hq.aestronglyMeasurable (nativeCollar_coefficient_bounded q hq).choose
    (nativeCollar_coefficient_bounded q hq).choose_spec.1
    ((ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet).mono
      (fun x hx => (nativeCollar_coefficient_bounded q hq).choose_spec.2 x hx))

theorem nativeCollarScalarMulCLM_ae (q : E → ℝ) (hq : Continuous q) (F : NativeCollarL2) :
    (nativeCollarScalarMulCLM q hq F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => q x*F x) :=
  l2ScalarMul_ae q hq.aestronglyMeasurable (nativeCollar_coefficient_bounded q hq).choose
    (nativeCollar_coefficient_bounded q hq).choose_spec.1
    ((ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet).mono
      (fun x hx => (nativeCollar_coefficient_bounded q hq).choose_spec.2 x hx)) F

theorem nativeCollarScalarMulCLM_norm_le (q : E → ℝ) (hq : Continuous q) {C : ℝ} (hC : 0≤C)
    (hb : ∀ x ∈ nativePoissonEntranceCollar,‖q x‖≤C) (F : NativeCollarL2) :
    ‖nativeCollarScalarMulCLM q hq F‖≤C*‖F‖ := by
  have hae : ∀ᵐ x ∂volume.restrict nativePoissonEntranceCollar,‖q x‖≤C :=
    (ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet).mono (fun x hx => hb x hx)
  have he : nativeCollarScalarMulCLM q hq F=l2ScalarMul q hq.aestronglyMeasurable C hC hae F := by
    apply Lp.ext
    exact (nativeCollarScalarMulCLM_ae q hq F).trans (l2ScalarMul_ae q hq.aestronglyMeasurable C hC hae F).symm
  rw [he]
  exact l2ScalarMul_norm_le q hq.aestronglyMeasurable C hC hae F

#print axioms nativeCollarScalarMulCLM_ae
#print axioms nativeCollarScalarMulCLM_norm_le
end Yamabe3.Analysis.SpherePolar
