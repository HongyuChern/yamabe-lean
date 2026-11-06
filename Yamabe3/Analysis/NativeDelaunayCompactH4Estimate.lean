import Yamabe3.Analysis.WeakFlatEquationH4Estimate
import Yamabe3.Analysis.NativeDelaunayH4Estimate
import Yamabe3.Analysis.DelaunayCompactPotentialJets

/-! The genuine weak H4 estimate is uniform before the Delaunay orbit and
phase. It keeps the same source and solution and the actual signed
annular potential. It is an interior estimate, not yet the weighted inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_weak_delaunay_compact_H4_estimate
    {O V W : Set E} (hO : IsOpen O) (hO0 : ∀ x ∈ O, x ≠ 0)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
      (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t, deriv (deriv v) t = radialForce (v t)) →
      ∀ (τ : ℝ) (u F : E → ℝ), MemWkpLocally 4 u O → MemWkp 2 2 F V →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, ∑ i : Fin 3, chosenWeakPartial' 2 i u V x*partialDeriv i φ x) =
          ∫ x in V, (F x-annularDelaunayPotential v τ x*u x)*φ x) →
      MemWkp 4 2 u W ∧ iteratedWeakSobolevNorm 4 2 u W ≤ C *
        (iteratedWeakSobolevNorm 0 2 u V+iteratedWeakSobolevNorm 2 2 F V) := by
  obtain ⟨Q,hQ,hQj⟩ := exists_uniform_delaunay_compact_potential_jets hVc (fun x hx => hO0 x (hVO hx)) 2
  obtain ⟨C,hC,hb⟩ := exists_uniform_weak_flat_equation_H4_estimate hV hVc hW hWc hWV hQ
  refine ⟨C,hC,?_⟩
  intro v hv hbound hODE τ u F hu hF heq
  let q : E → ℝ := fun x => -annularDelaunayPotential v τ x
  have hq : ContDiffOn ℝ ∞ q O := fun x hx =>
    (contDiffAt_annularDelaunayPotential hv τ (hO0 x hx)).neg.contDiffWithinAt
  refine hb O hO hVO q hq ?_ u F hu hF ?_
  · intro n hn x hx
    change ‖iteratedFDeriv ℝ n (-annularDelaunayPotential v τ) x‖ ≤ Q
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact hQj v hv hbound hODE τ n hn x (subset_closure hx)
  · simpa only [q, neg_mul, sub_eq_add_neg] using heq

#print axioms exists_uniform_weak_delaunay_compact_H4_estimate
end Yamabe3.Analysis.UniformElliptic
