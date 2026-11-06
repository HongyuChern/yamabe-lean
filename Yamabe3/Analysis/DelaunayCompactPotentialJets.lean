import Yamabe3.Analysis.DelaunayCompactParameterJets

/-! Uniform actual Delaunay potential jets on any fixed compact set away
from zero. This permits nested annuli without changing the source graph. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter Metric
open scoped ContDiff Topology
namespace Yamabe3.Analysis.Delaunay
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_delaunay_compact_potential_jets {K : Set E}
    (hK : IsCompact K) (hK0 : ∀ x ∈ K, x ≠ 0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
      (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t, deriv (deriv v) t = radialForce (v t)) →
      ∀ (τ : ℝ) (n : ℕ), n ≤ k → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (annularDelaunayPotential v τ) x‖ ≤ C := by
  obtain ⟨Φ,hΦ,-,-,horbit⟩ := exists_delaunay_state_flow
  let F : DelaunayState × E → ℝ := fun q =>
    -(15/4:ℝ)*(Φ (-Real.log ‖q.2‖) q.1).1^4/‖q.2‖^2
  have hF : ∀ q : DelaunayState × E, q.2 ∈ ({(0:E)}ᶜ : Set E) → ContDiffAt ℝ ∞ F q := by
    intro q hq
    have hq0 : q.2 ≠ 0 := by simpa using hq
    have hn : ContDiffAt ℝ ∞ (fun p : DelaunayState × E => ‖p.2‖) q :=
      (contDiffAt_norm ℝ hq0).comp q contDiffAt_snd
    have hl := ((Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hq0)).comp q hn).neg
    have hp := hΦ.contDiffAt.comp q (hl.prodMk contDiffAt_fst)
    exact (contDiffAt_const.mul (hp.fst.pow 4)).div (hn.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hq0))
  obtain ⟨C,hC,hb⟩ := exists_state_compact_spatial_jet_bound hK
    (show K ⊆ ({(0:E)}ᶜ : Set E) by intro x hx; simpa using hK0 x hx) hF k
  refine ⟨C,hC,?_⟩
  intro v hv hvb hODE τ n hn x hx
  have hs : ‖(v τ,deriv v τ)‖ ≤ (2:ℝ) := by
    simp only [Prod.norm_mk,Real.norm_eq_abs]
    apply max_le
    · rw [abs_of_nonneg (hvb τ).1]; linarith [(hvb τ).2.1]
    · linarith [(hvb τ).2.2]
  have he : annularDelaunayPotential v τ = fun y => F ((v τ,deriv v τ),y) := by
    funext y
    dsimp only [F,annularDelaunayPotential]
    rw [horbit v hv hvb hODE τ (-Real.log ‖y‖)]
    simp only [sub_eq_add_neg]
  rw [he]
  exact hb _ hs n hn x hx

#print axioms exists_uniform_delaunay_compact_potential_jets
end Yamabe3.Analysis.Delaunay
