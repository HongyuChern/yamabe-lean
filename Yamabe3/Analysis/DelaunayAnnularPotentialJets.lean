import Yamabe3.Analysis.DelaunayStateFlow
import Yamabe3.Analysis.Green.UniformResidualJets

/-!
# Uniform actual Delaunay potential jets on a fixed physical annulus

One complete smooth phase flow represents every time translate of every
actual bounded Delaunay orbit. Its state variable ranges over a fixed
compact set. The spatial derivatives of the genuine potential are
therefore bounded on the compact state/annulus product before any neck,
orbit or phase is chosen. No uniform parameter estimate is an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace Yamabe3.Analysis.Delaunay

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem joint_state_spatial_jet_smooth {F : DelaunayState × E3 → ℝ}
    (hF : ∀ q : DelaunayState × E3, q.2 ≠ 0 → ContDiffAt ℝ ∞ F q)
    (n : ℕ) (q : DelaunayState × E3) (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : DelaunayState × E3 =>
      iteratedFDeriv ℝ n (fun x => F (p.1, x)) p.2) q := by
  induction n generalizing q with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using!
      (hF q hq).continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ E3 ℝ).symm : _ →L[ℝ] E3 [×0]→L[ℝ] ℝ)
  | succ n ih =>
    have hh : ContDiffAt ℝ ∞
        (Function.uncurry (fun p : DelaunayState × E3 =>
          iteratedFDeriv ℝ n (fun x => F (p.1, x)))) (q, q.2) := by
      exact (ih (q.1, q.2) hq).comp (q, q.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun p : DelaunayState × E3 =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun x => F (p.1, x))) p.2) q :=
      hh.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using!
      hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E3) ℝ).symm :
          _ →L[ℝ] E3 [×(n + 1)]→L[ℝ] ℝ)

private theorem exists_state_annulus_jet_bound {F : DelaunayState × E3 → ℝ}
    (hF : ∀ q : DelaunayState × E3, q.2 ≠ 0 → ContDiffAt ℝ ∞ F q) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : DelaunayState, ‖s‖ ≤ 2 → ∀ z : E3,
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun x => F (s, x)) z‖ ≤ C := by
  let J : DelaunayState × E3 → E3 [×n]→L[ℝ] ℝ := fun q =>
    iteratedFDeriv ℝ n (fun x => F (q.1, x)) q.2
  let K : Set (DelaunayState × E3) := closedBall (0 : DelaunayState) 2 ×ˢ
    (closedBall (0 : E3) 2 \ ball (0 : E3) (1 / 2))
  have hK : IsCompact K := (isCompact_closedBall (0 : DelaunayState) 2).prod
    ((isCompact_closedBall (0 : E3) 2).diff isOpen_ball)
  have hJ : ContinuousOn J K := by
    intro q hq
    have hz : q.2 ≠ 0 := by
      intro heq
      apply hq.2.2
      simp [heq]
    exact (joint_state_spatial_jet_smooth hF n q hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := J) (by convert! hJ)
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro s hs z hzlo hzup
  apply (hC (s, z) ?_).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hs
  · simpa only [mem_closedBall, dist_zero_right] using hzup
  · simpa only [mem_ball, dist_zero_right, not_lt] using hzlo

/-- The potential in the actual physical equation after division by 8.
It is exactly minus 15/4 times the fourth power of the cylinder orbit
divided by the squared physical radius. -/
def annularDelaunayPotential (v : ℝ → ℝ) (τ : ℝ) (x : E3) : ℝ :=
  -(15 / 4 : ℝ) * v (τ - Real.log ‖x‖) ^ 4 / ‖x‖ ^ 2

theorem exists_uniform_delaunay_annular_potential_jets (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v : ℝ → ℝ), ContDiff ℝ ∞ v →
        (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1 / 2) →
        (∀ t, deriv (deriv v) t = radialForce (v t)) →
        ∀ (τ : ℝ) (n : ℕ), n ≤ k → ∀ z : E3,
          (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
          ‖iteratedFDeriv ℝ n (annularDelaunayPotential v τ) z‖ ≤ C := by
  obtain ⟨Φ, hΦ, _, _, horbit⟩ := exists_delaunay_state_flow
  let F : DelaunayState × E3 → ℝ := fun q =>
    -(15 / 4 : ℝ) * (Φ (-Real.log ‖q.2‖) q.1).1 ^ 4 / ‖q.2‖ ^ 2
  have hF : ∀ q : DelaunayState × E3, q.2 ≠ 0 → ContDiffAt ℝ ∞ F q := by
    intro q hq
    have hn : ContDiffAt ℝ ∞ (fun z : DelaunayState × E3 => ‖z.2‖) q :=
      (contDiffAt_norm ℝ hq).comp q contDiffAt_snd
    have hl : ContDiffAt ℝ ∞ (fun z : DelaunayState × E3 => -Real.log ‖z.2‖) q :=
      ((Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hq)).comp q hn).neg
    have hp := hΦ.contDiffAt.comp q (hl.prodMk contDiffAt_fst)
    exact (contDiffAt_const.mul (hp.fst.pow 4)).div (hn.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hq))
  choose C hC hbound using fun n => exists_state_annulus_jet_bound hF n
  refine ⟨∑ n ∈ Finset.range (k + 1), C n,
    Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro v hv hb hODE τ n hn z hzlo hzup
  have hs : ‖(v τ, deriv v τ)‖ ≤ (2 : ℝ) := by
    simp only [Prod.norm_mk, Real.norm_eq_abs]
    apply max_le
    · rw [abs_of_nonneg (hb τ).1]
      linarith [(hb τ).2.1]
    · linarith [(hb τ).2.2]
  have heq : annularDelaunayPotential v τ = fun x => F ((v τ, deriv v τ), x) := by
    funext x
    dsimp only [F, annularDelaunayPotential]
    rw [horbit v hv hb hODE τ (-Real.log ‖x‖)]
    simp only [sub_eq_add_neg]
  rw [heq]
  exact (hbound n (v τ, deriv v τ) hs z hzlo hzup).trans
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

#print axioms exists_uniform_delaunay_annular_potential_jets

end Yamabe3.Analysis.Delaunay
