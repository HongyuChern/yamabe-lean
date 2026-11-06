import Yamabe3.Analysis.WeakFlatH4Estimate
import Yamabe3.Analysis.WeakLaplacianEquation

/-! The uniform H4 estimate now uses the original weak equation and its
actual H2 source. The locally smooth potential is genuinely extended only
for approximation; its germs and original source are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_weak_flat_equation_H4_estimate
    {V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V)
    {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (O : Set E), IsOpen O → closure V ⊆ O →
      ∀ q : E → ℝ, ContDiffOn ℝ ∞ q O →
      (∀ n ≤ 2, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q x‖ ≤ Q) →
      ∀ u F : E → ℝ, MemWkpLocally 4 u O → MemWkp 2 2 F V →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, ∑ i : Fin 3, chosenWeakPartial' 2 i u V x*partialDeriv i φ x) =
          ∫ x in V, (F x+q x*u x)*φ x) →
      MemWkp 4 2 u W ∧ iteratedWeakSobolevNorm 4 2 u W ≤ C *
        (iteratedWeakSobolevNorm 0 2 u V+iteratedWeakSobolevNorm 2 2 F V) := by
  obtain ⟨C,hC,hb⟩ := exists_uniform_weak_flat_H4_estimate hV hVc hW hWc hWV hQ
  refine ⟨C,hC,?_⟩
  intro O hO hVO q hq hqj u F hu hF heq
  obtain ⟨q₀,hq₀,-,hg⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hq
  have hqeq (x : E) (hx : x ∈ V) : q₀ x = q x := (hg x (subset_closure hx)).self_of_nhds
  have hq₀j : ∀ n ≤ 2, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q₀ x‖ ≤ Q := by
    intro n hn x hx
    rw [((hg x (subset_closure hx)).iteratedFDeriv ℝ n).self_of_nhds]
    exact hqj n hn x hx
  have hu4 := memWkp_on_precompact_of_locally hu hV hVc hVO
  have hu2 := hu4.le_of_le (by norm_num : 2 ≤ 4)
  have hqu : MemLp (fun x => q₀ x*u x) 2 (volume.restrict V) :=
    memWkp_mul_smooth_of_isCompact_closure 0 hV hVc hu2.memLp hq₀
  have heq₀ : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, ∑ i : Fin 3, chosenWeakPartial' 2 i u V x*partialDeriv i φ x) =
        ∫ x in V, (F x+q₀ x*u x)*φ x := by
    intro φ hφ hc hs
    rw [heq φ hφ hc hs]
    apply setIntegral_congr_fun hV.measurableSet
    intro x hx
    change (F x+q x*u x)*φ x = (F x+q₀ x*u x)*φ x
    rw [hqeq x hx]
  have hl := weakNegativeLaplacian_eq_source_ae hV hu2
    ((hF.memLp.add hqu).locallyIntegrable (by norm_num)) heq₀
  have hFae : weakFlatOperator V q₀ u =ᵐ[volume.restrict V] F := by
    filter_upwards [hl] with x hx
    simp only [weakFlatOperator, hx, Pi.add_apply, add_sub_cancel_right]
  have hn := hb q₀ hq₀ hq₀j u hVO hu
  rw [wkpNorm_congr_ae (k := 2) (by norm_num) hV hFae] at hn
  exact ⟨memWkp_on_precompact_of_locally hu hW hWc (hWV.trans (subset_closure.trans hVO)),hn⟩

#print axioms exists_uniform_weak_flat_equation_H4_estimate
end Yamabe3.Analysis.UniformElliptic
