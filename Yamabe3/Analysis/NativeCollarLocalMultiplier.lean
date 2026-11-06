import Yamabe3.Analysis.NativeCollarScalarMultiplier

/-! Coefficients continuous away from the puncture act on the actual
entrance collar L2 space. No value or bound at the puncture is required. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology
namespace Yamabe3.Analysis.SpherePolar

private theorem local_bounded (q : E → ℝ) (hq : ContinuousOn q {x | x ≠ 0}) :
    ∃ C : ℝ,0≤C ∧ ∀ x ∈ nativePoissonEntranceCollar,‖q x‖≤C := by
  obtain ⟨C,hC⟩ := (nativePolarTimeWindow_precompact (1/2)).exists_bound_of_continuousOn
    (hq.mono (nativePolarTimeWindow_closure_offZero (1/2)))
  exact ⟨max C 0,le_max_right _ _,fun x hx => (hC x (subset_closure hx)).trans (le_max_left _ _)⟩

private theorem local_measurable (q : E → ℝ) (hq : ContinuousOn q {x | x ≠ 0}) :
    AEStronglyMeasurable q (volume.restrict nativePoissonEntranceCollar) :=
  (hq.mono (subset_closure.trans (nativePolarTimeWindow_closure_offZero (1/2)))).aestronglyMeasurable
    (nativePolarTimeWindow_open (1/2)).measurableSet

def nativeCollarLocalMulCLM (q : E → ℝ) (hq : ContinuousOn q {x | x ≠ 0}) :
    NativeCollarL2 →L[ℝ] NativeCollarL2 :=
  l2ScalarMulCLM q (local_measurable q hq) (local_bounded q hq).choose
    (local_bounded q hq).choose_spec.1
    ((ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet).mono
      (fun x hx => (local_bounded q hq).choose_spec.2 x hx))

theorem nativeCollarLocalMulCLM_ae (q : E → ℝ) (hq : ContinuousOn q {x | x ≠ 0}) (F : NativeCollarL2) :
    (nativeCollarLocalMulCLM q hq F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => q x*F x) :=
  l2ScalarMul_ae q (local_measurable q hq) (local_bounded q hq).choose
    (local_bounded q hq).choose_spec.1
    ((ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet).mono
      (fun x hx => (local_bounded q hq).choose_spec.2 x hx)) F

theorem nativeCollarLocalMulCLM_norm_le (q : E → ℝ) (hq : ContinuousOn q {x | x ≠ 0})
    {C : ℝ} (hC : 0≤C) (hb : ∀ x ∈ nativePoissonEntranceCollar,‖q x‖≤C) (F : NativeCollarL2) :
    ‖nativeCollarLocalMulCLM q hq F‖≤C*‖F‖ := by
  have hae : ∀ᵐ x ∂volume.restrict nativePoissonEntranceCollar,‖q x‖≤C :=
    (ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet).mono (fun x hx => hb x hx)
  have he : nativeCollarLocalMulCLM q hq F=l2ScalarMul q (local_measurable q hq) C hC hae F := by
    apply Lp.ext
    exact (nativeCollarLocalMulCLM_ae q hq F).trans (l2ScalarMul_ae q (local_measurable q hq) C hC hae F).symm
  rw [he]
  exact l2ScalarMul_norm_le q (local_measurable q hq) C hC hae F

#print axioms nativeCollarLocalMulCLM_ae
#print axioms nativeCollarLocalMulCLM_norm_le
end Yamabe3.Analysis.SpherePolar
