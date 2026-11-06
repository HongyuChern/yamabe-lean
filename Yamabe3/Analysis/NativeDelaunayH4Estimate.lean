import Yamabe3.Analysis.UniformElliptic.LocalUniformSobolev
import Yamabe3.Analysis.UniformElliptic.LocalDivergenceEquation
import Yamabe3.Analysis.UniformElliptic.NativeDelaunayOperatorError
import Yamabe3.Analysis.Cylinder.EuclideanJacobiEnergy

/-!
# A uniform gain of two derivatives for the literal flat Delaunay operator

The constant precedes the orbit and its phase.  The coefficient jets are
obtained from the actual bounded Delaunay ODE, and the weak equation is
derived from the pointwise operator equation by integration by parts.
This is an interior estimate, not yet a half-end inverse or collar extension.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT Delaunay SpherePolar
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The actual identity principal form has uniformly bounded jets of all
orders.  This bound supplies, rather than assumes, the principal estimate. -/
theorem euclideanPrincipalForm_all_jet_bound (Ω : Set E3) (n : ℕ)
    (x : E3) (i j : Fin 3) :
    ‖iteratedFDeriv ℝ n (fun y => (euclideanPrincipalForm Ω).a y i j) x‖ ≤ 1 := by
  cases n with
  | zero => simpa using euclideanPrincipalForm_entry_bound Ω x i j
  | succ n => simp [euclideanPrincipalForm, iteratedFDeriv_succ_const]

/-- A genuine source of order two controls four derivatives of the same
smooth local solution.  No potential bound depending on the orbit or phase
is supplied by the caller.  The domains are fixed before the constant. -/
theorem exists_uniform_flat_delaunay_H4_estimate
    {O V W : Set E3} (hO : IsOpen O) (hO0 : ∀ x ∈ O, x ≠ 0)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hVann : ∀ x ∈ V, (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
      (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1 / 2) →
      (∀ t, deriv (deriv v) t = radialForce (v t)) →
      ∀ τ : ℝ, ∀ u f : E3 → ℝ,
        ContDiffOn ℝ ∞ u O → ContDiffOn ℝ ∞ f O →
        (∀ x ∈ V, flatDelaunayJacobian v τ u x = f x) →
        derivativeProfile 2 W 4 u ≤ ENNReal.ofReal C *
          (derivativeProfile 2 V 0 u + derivativeProfile 2 V 2 f) := by
  obtain ⟨Q, hQ, hQjet⟩ := exists_uniform_delaunay_annular_potential_jets 2
  obtain ⟨C, hC, hbound⟩ := exists_local_uniform_derivativeProfile_add_two_with_potential
    2 hO hV hVc hVO (Ω := O) hVO hW hWc hWV
    (κ := 1) (L := 1) (Q := Q) (by norm_num) (by norm_num) hQ
  refine ⟨C, hC, ?_⟩
  intro v hv hb hODE τ u f hu hf heq
  let q : E3 → ℝ := fun x => -annularDelaunayPotential v τ x
  have hqs : ContDiffOn ℝ ∞ q O := fun x hx =>
    (contDiffAt_annularDelaunayPotential hv τ (hO0 x hx)).neg.contDiffWithinAt
  have hqj (n : ℕ) (hn : n ≤ 2) (x : E3) (hx : x ∈ V) :
      ‖iteratedFDeriv ℝ n q x‖ ≤ Q := by
    change ‖iteratedFDeriv ℝ n (-annularDelaunayPotential v τ) x‖ ≤ Q
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact hQjet v hv hb hODE τ n hn x (hVann x hx).1 (hVann x hx).2
  have hweak : WeakEquation V
      (matrixFlux (euclideanPrincipalForm O).a (fun j => partialDeriv j u))
      (fun x => f x + q x * u x) := by
    apply weakEquation_of_local_principalSource
      (a := fun _ : E3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) hO hV hVc hVO
      (fun _ _ => contDiff_const) hu
    intro x hx
    have h := heq x hx
    dsimp only [flatDelaunayJacobian] at h
    change principalSource (fun _ : E3 => 1) u x =
      f x + (-annularDelaunayPotential v τ x) * u x
    linarith
  exact hbound (euclideanPrincipalForm O) le_rfl
    (fun n _ x _ i j => euclideanPrincipalForm_all_jet_bound O n x i j)
    (by intro x hx; simp [euclideanPrincipalForm]) q hqs hqj hu hf hweak

#print axioms exists_uniform_flat_delaunay_H4_estimate

end Yamabe3.Analysis.UniformElliptic
