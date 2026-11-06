import Yamabe3.Analysis.WeakDivergenceSourceIdentity

/-! A weak equation on all actual precompact subdomains is the same weak
equation on the open domain. The test and its derivatives vanish outside
one selected precompact neighborhood of its compact support. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakEquation_of_precompact_local {O : Set E} (hO : IsOpen O)
    (F : Fin d→E→ℝ) (f : E→ℝ)
    (hlocal : ∀W : Set E,IsOpen W → IsCompact (closure W) → closure W⊆O → WeakEquation W F f) :
    WeakEquation O F f := by
  intro φ hφ hc hs
  obtain ⟨W,hW,hφW,hWO,hWc⟩ := exists_open_between_and_isCompact_closure hc hO hs
  have hleft : (∫x in O,∑i : Fin d,F i x*partialDeriv i φ x)=
      ∫x in W,∑i : Fin d,F i x*partialDeriv i φ x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hO.measurableSet (subset_closure.trans hWO)
    intro x hx
    have hn : x∉tsupport φ := fun ht => hx.2 (hφW ht)
    simp only [partialDeriv,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply,mul_zero,Finset.sum_const_zero]
  have hright : (∫x in O,f x*φ x)=∫x in W,f x*φ x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hO.measurableSet (subset_closure.trans hWO)
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx.2 (hφW ht)),mul_zero]
  exact hleft.trans ((hlocal W hW hWc hWO φ hφ hc hφW).trans hright.symm)

#print axioms weakEquation_of_precompact_local
end Yamabe3.Analysis.UniformElliptic
