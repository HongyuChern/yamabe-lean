import Yamabe3.Analysis.Green.RescaledResidual

/-!
# Uniform bounds of every fixed spatial order for the rescaled source

Joint smoothness is differentiated in the spatial variable with the scale
retained as a parameter. Compactness is then applied before selecting the
scale. These are derivatives of the actual source family, not an assumed
uniform estimate for inverses of elliptic operators.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace Yamabe3.Analysis.GreenParametrix

theorem contDiffAt_spatial_jet_of_joint_smooth {F : ℝ × E → ℝ}
    (hF : ∀ q : ℝ × E, q.2 ≠ 0 → ContDiffAt ℝ ∞ F q)
    (n : ℕ) (q : ℝ × E) (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E =>
      iteratedFDeriv ℝ n (fun x => F (p.1, x)) p.2) q := by
  induction n generalizing q with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using!
      (hF q hq).continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ E ℝ).symm : _ →L[ℝ] E [×0]→L[ℝ] ℝ)
  | succ n ih =>
    have hh : ContDiffAt ℝ ∞
        (Function.uncurry (fun p : ℝ × E =>
          iteratedFDeriv ℝ n (fun x => F (p.1, x))))
        (q, q.2) := by
      exact (ih (q.1, q.2) hq).comp (q, q.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun x => F (p.1, x))) p.2) q :=
      hh.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using!
      hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm :
          _ →L[ℝ] E [×(n + 1)]→L[ℝ] ℝ)

/-- Every fixed spatial derivative has one bound on the whole compact scale
interval and annulus, with the constant selected before the scale. -/
theorem exists_uniform_spatial_jet_bound {F : ℝ × E → ℝ}
    (hF : ∀ q : ℝ × E, q.2 ≠ 0 → ContDiffAt ℝ ∞ F q)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0 : ℝ) 1, ∀ z : E,
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun x => F (r, x)) z‖ ≤ C := by
  let J : ℝ × E → E [×n]→L[ℝ] ℝ := fun q =>
    iteratedFDeriv ℝ n (fun x => F (q.1, x)) q.2
  let K : Set (ℝ × E) := Icc (0 : ℝ) 1 ×ˢ
    (closedBall (0 : E) 2 \ ball (0 : E) (1 / 2))
  have hK : IsCompact K := isCompact_Icc.prod
    ((isCompact_closedBall (0 : E) 2).diff isOpen_ball)
  have hJ : ContinuousOn J K := by
    intro q hq
    have hz : q.2 ≠ 0 := by
      intro heq
      apply hq.2.2
      simp [heq]
    exact (contDiffAt_spatial_jet_of_joint_smooth hF n q hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := J) (by convert! hJ)
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro r hr z hzlo hzup
  apply (hC (r, z) ?_).trans (le_max_right _ _)
  refine ⟨hr, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hzup
  · simpa only [mem_ball, dist_zero_right, not_lt] using hzlo

/-- A single constant controls every order up to the specified finite k. -/
theorem exists_uniform_spatial_jet_bounds {F : ℝ × E → ℝ}
    (hF : ∀ q : ℝ × E, q.2 ≠ 0 → ContDiffAt ℝ ∞ F q) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ k, ∀ r ∈ Icc (0 : ℝ) 1, ∀ z : E,
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun x => F (r, x)) z‖ ≤ C := by
  classical
  choose C hC hbound using fun n => exists_uniform_spatial_jet_bound hF n
  refine ⟨∑ n ∈ Finset.range (k + 1), C n,
    Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro n hn r hr z hzlo hzup
  exact (hbound n r hr z hzlo hzup).trans
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

theorem contDiffAt_scaledDensityResidual_spatial_jet {ρ V : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) (hV : ContDiff ℝ ∞ V)
    (n : ℕ) (q : ℝ × E) (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E =>
      iteratedFDeriv ℝ n (fun x => scaledDensityResidual ρ V (p.1, x)) p.2) q :=
  contDiffAt_spatial_jet_of_joint_smooth
    (contDiffAt_scaledDensityResidual hρ hpos hV) n q hq

theorem exists_uniform_scaledDensityResidual_jet_bound {ρ V : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) (hV : ContDiff ℝ ∞ V) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0 : ℝ) 1, ∀ z : E,
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun x => scaledDensityResidual ρ V (r, x)) z‖ ≤ C :=
  exists_uniform_spatial_jet_bound (contDiffAt_scaledDensityResidual hρ hpos hV) n

/-- The volume-weighted forcing in the genuine divergence-form equation. -/
def weightedScaledDensityResidual (ρ V : E → ℝ) (q : ℝ × E) : ℝ :=
  ρ (q.1 • q.2) * scaledDensityResidual ρ V q

theorem contDiffAt_weightedScaledDensityResidual {ρ V : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x) (hV : ContDiff ℝ ∞ V)
    (q : ℝ × E) (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (weightedScaledDensityResidual ρ V) q := by
  exact (hρ.contDiffAt.comp q (contDiffAt_fst.smul contDiffAt_snd)).mul
    (contDiffAt_scaledDensityResidual hρ hpos hV q hq)

#print axioms contDiffAt_spatial_jet_of_joint_smooth
#print axioms exists_uniform_spatial_jet_bound
#print axioms exists_uniform_spatial_jet_bounds
#print axioms contDiffAt_scaledDensityResidual_spatial_jet
#print axioms exists_uniform_scaledDensityResidual_jet_bound
#print axioms contDiffAt_weightedScaledDensityResidual

end Yamabe3.Analysis.GreenParametrix
