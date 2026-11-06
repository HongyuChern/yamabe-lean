import Yamabe3.Analysis.UniformElliptic.H4CauchyRepresentative
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Constructing the same C2 limit of a locally H4-Cauchy smooth sequence

Every point value is first proved Cauchy using the actual local H4
embedding, and its limit is constructed in the complete scalar field.
The previously proved representative theorem then identifies the actual
two-jets of this single function on every compact neighborhood. No global
H4 completion, dense smooth uniform-local Sobolev class, or classical
fourth derivatives of the limit are asserted.

This permits a direct smooth-iteration limit argument once the actual
coupled inverse and its contraction estimates have been proved.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem exists_precompact_open_ball_neighborhood
    {O : Set E3} (hO : IsOpen O) {x : E3} (hx : x ∈ O) :
    ∃ V : Set E3, IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ O ∧ x ∈ V := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hO x hx
  refine ⟨ball x (r / 2), isOpen_ball, ?_, ?_, mem_ball_self (half_pos hr)⟩
  · exact (isCompact_closedBall x (r / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  · exact closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (half_lt_self hr)).trans hb)

/-- Construct the pointwise limit and its actual derivatives through
order two, using only the real local H4-Cauchy property of the sequence.
The limit on the open region is unique by scalar Hausdorff uniqueness. -/
theorem exists_same_c2_limit_of_locally_h4_cauchy
    {O : Set E3} (hO : IsOpen O) (u : ℕ → E3 → ℝ)
    (hu : ∀ n, ContDiffOn ℝ ∞ (u n) O)
    (hCauchy : ∀ V : Set E3, IsOpen V → IsCompact (closure V) → closure V ⊆ O →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        (derivativeProfile 2 V 4 (fun x => u n x - u m x)).toReal ≤ ε) :
    ∃ U : E3 → ℝ, ContDiffOn ℝ 2 U O ∧
      (∀ x ∈ O, Tendsto (fun n => u n x) atTop (𝓝 (U x)) ∧
        ∀ j ≤ 2, Tendsto (fun n => iteratedFDeriv ℝ j (u n) x)
          atTop (𝓝 (iteratedFDeriv ℝ j U x))) ∧
      (∀ W : E3 → ℝ,
        (∀ x ∈ O, Tendsto (fun n => u n x) atTop (𝓝 (W x))) → EqOn U W O) := by
  classical
  have hscalar (x : E3) (hx : x ∈ O) : CauchySeq (fun n => u n x) := by
    obtain ⟨V, hV, hVc, hVO, hxV⟩ := exists_precompact_open_ball_neighborhood hO hx
    obtain ⟨C, hC, hjets⟩ := exists_local_h4_sup_two_jet_bound_on_compact
      (isCompact_singleton : IsCompact ({x} : Set E3)) hV hVc hO hVO
        (singleton_subset_iff.mpr hxV)
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hCauchy V hV hVc hVO (ε / (2 * C)) (by positivity)
    refine ⟨N, ?_⟩
    intro n hn m hm
    have hb := hjets ((hu n).sub (hu m)) 0 (by norm_num) x (mem_singleton x)
    rw [norm_iteratedFDeriv_zero] at hb
    have hdist : dist (u n x) (u m x) ≤ ε / 2 := by
      calc
        _ ≤ C * (derivativeProfile 2 V 4 (fun y => u n y - u m y)).toReal := by
          simpa only [dist_eq_norm] using hb
        _ ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left (hN n m hn hm) hC.le
        _ = ε / 2 := by field_simp [hC.ne']
    exact hdist.trans_lt (half_lt_self hε)
  have hexists (x : O) : ∃ y : ℝ, Tendsto (fun n => u n x) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (hscalar x x.2)
  choose U₀ hU₀ using hexists
  let U : E3 → ℝ := fun x => if hx : x ∈ O then U₀ ⟨x, hx⟩ else 0
  have hpoint (x : E3) (hx : x ∈ O) : Tendsto (fun n => u n x) atTop (𝓝 (U x)) := by
    simpa only [U, dif_pos hx] using hU₀ ⟨x, hx⟩
  have hjet (x : E3) (hx : x ∈ O) : ContDiffAt ℝ 2 U x ∧
      ∀ j ≤ 2, Tendsto (fun n => iteratedFDeriv ℝ j (u n) x)
        atTop (𝓝 (iteratedFDeriv ℝ j U x)) := by
    obtain ⟨V, hV, hVc, hVO, hxV⟩ := exists_precompact_open_ball_neighborhood hO hx
    have h := contDiffAt_two_of_local_h4_cauchy_of_pointwise_limit
      (isCompact_singleton : IsCompact ({x} : Set E3)) hV hVc hO hVO
        (singleton_subset_iff.mpr hxV) u hu (hCauchy V hV hVc hVO) U hpoint
    exact h.2 x (mem_singleton x)
  refine ⟨U, (fun x hx => (hjet x hx).1.contDiffWithinAt),
    (fun x hx => ⟨hpoint x hx, (hjet x hx).2⟩), ?_⟩
  intro W hW x hx
  exact tendsto_nhds_unique (hpoint x hx) (hW x hx)

#print axioms exists_same_c2_limit_of_locally_h4_cauchy

end Yamabe3.Analysis.UniformElliptic
