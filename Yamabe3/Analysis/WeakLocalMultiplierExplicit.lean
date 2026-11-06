import Yamabe3.Analysis.WeakMultiplierExplicit
import Yamabe3.Analysis.UniformElliptic.LocalUniformJet

/-! The quantitative weak multiplier estimate only needs smoothness near
the integration closure. Extension preserves the actual coefficient jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weak_local_multiplier_explicit_bound (k : ℕ) {O W : Set E}
    (hO : IsOpen O) (hOc : IsCompact (closure O)) (hW : IsOpen W) (hOW : closure O ⊆ W)
    {a u : E → ℝ} (ha : ContDiffOn ℝ ∞ a W) (hu : MemWkp k 2 u O)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hj : ∀ j ≤ k, ∀ x ∈ O, ‖iteratedFDeriv ℝ j a x‖ ≤ Q) :
    MemWkp k 2 (fun x => a x*u x) O ∧
      iteratedWeakSobolevNorm k 2 (fun x => a x*u x) O ≤
        ((1+2*(d:ℝ≥0∞))^k*ENNReal.ofReal Q)*iteratedWeakSobolevNorm k 2 u O := by
  obtain ⟨b,hb,-,he⟩ := exists_smooth_compact_extension_near_compact hW hOc hOW ha
  have hjb : ∀ j ≤ k, ∀ x ∈ O, ‖iteratedFDeriv ℝ j b x‖ ≤ Q := by
    intro j hjk x hx
    rw [((he x (subset_closure hx)).iteratedFDeriv ℝ j).self_of_nhds]
    exact hj j hjk x hx
  have heq : (fun x => b x*u x) =ᵐ[volume.restrict O] fun x => a x*u x := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    rw [(he x (subset_closure hx)).self_of_nhds]
  refine ⟨(MemWkp_congr_ae (by norm_num) hO heq).mp
    (memWkp_mul_smooth_of_isCompact_closure k hO hOc hu hb),?_⟩
  rw [← wkpNorm_congr_ae (k := k) (by norm_num) hO heq]
  exact weak_sobolev_multiplier_explicit_bound k hO hOc hQ b hb hjb u hu

#print axioms weak_local_multiplier_explicit_bound
end Yamabe3.Analysis.UniformElliptic
