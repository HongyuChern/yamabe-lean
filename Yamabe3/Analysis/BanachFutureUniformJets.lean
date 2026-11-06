import Yamabe3.Analysis.BanachFutureObservable

/-! Uniform first and second strong derivatives of the same future
fixed point at weight two. The bounds use the actual resolvent equation,
not an input bound on derivatives of the potential or source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem banachFuturePotentialInverse_first_deriv {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k^2) (F : ℝ →ᵇ H) (t : ℝ) :
    let u := banachFuturePotentialInverse k hk A hA F
    deriv (fun s => u s) t = k • u t-
      banachFutureResolvent k hk (F+boundedOperatorAction A u) t := by
  dsimp only
  let u := banachFuturePotentialInverse k hk A hA F
  have he : (fun t => banachDoubleFutureResolvent k hk (F+boundedOperatorAction A u) t) =
      fun t => u t := congrArg (fun G : ℝ →ᵇ H => (fun t => G t))
        (banachFuturePotentialInverse_fixed hk A hA F)
  have hd := (banachDoubleFutureResolvent_equation hk (F+boundedOperatorAction A u)).2.2.1 t
  dsimp only at hd
  rw [he,congrFun he t] at hd
  exact hd

theorem banachFuturePotentialInverse_two_jets
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ ≤ 7/2) (F : ℝ →ᵇ H) :
    let u := banachFuturePotentialInverse 2 (by norm_num) A (by linarith) F
    ‖u‖ ≤ 2*‖F‖ ∧
    (∀ t, ‖deriv (fun s => u s) t‖ ≤ 8*‖F‖) ∧
    (∀ t, ‖deriv (deriv (fun s => u s)) t‖ ≤ 48*‖F‖) := by
  dsimp only
  let u := banachFuturePotentialInverse 2 (by norm_num) A (by linarith) F
  have hg : ‖A‖ < (2:ℝ)^2 := by linarith
  have hu : ‖u‖ ≤ 2*‖F‖ := by
    have hh := banachFuturePotentialInverse_norm_le (by norm_num : (0:ℝ)<2) A hg F
    change ‖u‖ ≤ _ at hh
    have hd : 0 < (2:ℝ)^2-‖A‖ := by linarith
    have hm := (le_div_iff₀ hd).mp hh
    nlinarith [norm_nonneg u]
  let G := F+boundedOperatorAction A u
  have hG : ‖G‖ ≤ 8*‖F‖ := by
    calc
      _ ≤ ‖F‖+‖A‖*‖u‖ := (norm_add_le _ _).trans
        (add_le_add le_rfl (boundedOperatorAction_norm_le A u))
      _ ≤ ‖F‖+(7/2)*(2*‖F‖) := add_le_add le_rfl
        (mul_le_mul hA hu (norm_nonneg u) (by norm_num))
      _ = _ := by ring
  have h1 (t : ℝ) : ‖deriv (fun s => u s) t‖ ≤ 8*‖F‖ := by
    have hd := banachFuturePotentialInverse_first_deriv (by norm_num : (0:ℝ)<2) A hg F t
    change deriv (fun s => u s) t = (2:ℝ) • u t-banachFutureResolvent 2 (by norm_num) G t at hd
    rw [hd]
    have hr := (BoundedContinuousFunction.norm_coe_le_norm (banachFutureResolvent 2 (by norm_num) G) t).trans
      (banachFutureResolvent_norm_le (by norm_num : (0:ℝ)<2) G)
    have hup := (u.norm_coe_le_norm t).trans hu
    calc
      _ ≤ ‖(2:ℝ) • u t‖+‖banachFutureResolvent 2 (by norm_num) G t‖ := norm_sub_le _ _
      _ = 2*‖u t‖+‖banachFutureResolvent 2 (by norm_num) G t‖ := by rw [norm_smul]; norm_num
      _ ≤ 8*‖F‖ := by linarith
  refine ⟨hu,h1,?_⟩
  intro t
  have he := (banachFuturePotentialInverse_equation (by norm_num : (0:ℝ)<2) A hg F).2.2 t
  change deriv (deriv (fun s => u s)) t = (2*2:ℝ) • deriv (fun s => u s) t-
    (2:ℝ)^2 • u t+F t+A t (u t) at he
  have hAu : ‖A t (u t)‖ ≤ (7/2)*(2*‖F‖) :=
    ((A t).le_opNorm _).trans (mul_le_mul ((A.norm_coe_le_norm t).trans hA)
      ((u.norm_coe_le_norm t).trans hu) (norm_nonneg _) (by norm_num))
  rw [he]
  calc
    _ ≤ ‖(2*2:ℝ) • deriv (fun s => u s) t-(2:ℝ)^2 • u t‖+‖F t‖+‖A t (u t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖(2*2:ℝ) • deriv (fun s => u s) t‖+‖(2:ℝ)^2 • u t‖)+‖F t‖+‖A t (u t)‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ 48*‖F‖ := by
      simp only [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2*2),
        Real.norm_of_nonneg (sq_nonneg (2:ℝ))]
      have h := h1 t
      have hut := (u.norm_coe_le_norm t).trans hu
      have hFt := F.norm_coe_le_norm t
      nlinarith

#print axioms banachFuturePotentialInverse_first_deriv
#print axioms banachFuturePotentialInverse_two_jets
end Yamabe3.Analysis.Delaunay
