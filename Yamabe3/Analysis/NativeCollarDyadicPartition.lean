import Yamabe3.Analysis.NativeShellCutoff

/-! A real smooth radial-scale partition with compact collar pieces.
The shrinking remainder vanishes pointwise off the puncture, and all
finite sums telescope on the SAME physical function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar

def nativeCollarDyadicPiece (χ:E→ℝ):E→ℝ := fun x=>χ x-χ (Real.exp (1/4:ℝ) • x)
def nativeCollarDyadicCutoff (χ:E→ℝ) (n:ℕ):E→ℝ := fun x=>χ (Real.exp ((n:ℝ)/4) • x)

theorem nativeCollarDyadicPiece_smooth {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (nativeCollarDyadicPiece χ) :=
  hχ.sub (hχ.comp (contDiff_id.const_smul _))

theorem nativeCollarDyadicPiece_compact {χ:E→ℝ} (hc:HasCompactSupport χ) :
    HasCompactSupport (nativeCollarDyadicPiece χ) :=
  hc.sub (hc.comp_homeomorph (Homeomorph.smulOfNeZero (Real.exp (1/4:ℝ)) (Real.exp_ne_zero _)))

theorem nativeCollarDyadicPiece_support {χ:E→ℝ}
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1)) :
    tsupport (nativeCollarDyadicPiece χ)⊆nativePoissonEntranceCollar := by
  intro x hx
  have hlow:Real.exp (-(3/8:ℝ)) < ‖x‖ := by
    by_contra hh
    have hn:‖x‖ ≤ Real.exp (-(3/8:ℝ)) := le_of_not_gt hh
    have hx1:x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))) := by
      rw [mem_closedBall,dist_zero_right]
      exact hn.trans (Real.exp_le_exp.mpr (by norm_num))
    have hx2:Real.exp (1/4:ℝ) • x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))) := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le).trans_eq (by rw [←Real.exp_add];norm_num)
    have he: (fun y:E=>χ (Real.exp (1/4:ℝ) • y))=ᶠ[𝓝 x](fun _=>1) :=
      (continuous_const_smul (Real.exp (1/4:ℝ))).continuousAt.tendsto.eventually (h1 _ hx2)
    have hz:nativeCollarDyadicPiece χ=ᶠ[𝓝 x](fun _=>0) := by
      filter_upwards [h1 x hx1,he] with y hy he
      change χ y-χ (Real.exp (1/4:ℝ) • y)=0
      rw [hy,he]
      simp only [Pi.zero_apply,sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  have hu:‖x‖ < Real.exp (1/8:ℝ) := by
    by_contra hh
    have hn:Real.exp (1/8:ℝ) ≤ ‖x‖ := le_of_not_gt hh
    have hx1:x∉tsupport χ := fun h=>not_lt_of_ge hn (mem_ball_zero_iff.mp (hs h))
    have hx2:Real.exp (1/4:ℝ) • x∉tsupport χ := by
      intro h
      have hb:=mem_ball_zero_iff.mp (hs h)
      rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hb
      have he:1 ≤ Real.exp (1/4:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
      have hn':‖x‖ ≤ Real.exp (1/4:ℝ)*‖x‖ := by nlinarith [norm_nonneg x]
      linarith
    have he:(fun y:E=>χ (Real.exp (1/4:ℝ) • y))=ᶠ[𝓝 x](fun _=>0) :=
      (continuous_const_smul (Real.exp (1/4:ℝ))).continuousAt.tendsto.eventually
        (notMem_tsupport_iff_eventuallyEq.mp hx2)
    have hz:nativeCollarDyadicPiece χ=ᶠ[𝓝 x](fun _=>0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx1,he] with y hy he
      change χ y-χ (Real.exp (1/4:ℝ) • y)=0
      rw [hy,he]
      simp only [Pi.zero_apply,sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  exact (nativePolarTimeWindow_norm (1/2) x).mpr
    ⟨(Real.exp_lt_exp.mpr (by norm_num:-(1/2:ℝ) < -(3/8:ℝ))).trans hlow,
      hu.trans (Real.exp_lt_exp.mpr (by norm_num:(1/8:ℝ) < 1/2))⟩

theorem nativeCollarDyadicPiece_scale (χ:E→ℝ) (n:ℕ) (x:E) :
    nativeCollarDyadicPiece χ (Real.exp ((n:ℝ)/4) • x)=
      nativeCollarDyadicCutoff χ n x-nativeCollarDyadicCutoff χ (n+1) x := by
  dsimp only [nativeCollarDyadicPiece,nativeCollarDyadicCutoff]
  rw [smul_smul,←Real.exp_add]
  congr 3
  push_cast
  ring

theorem nativeCollarDyadicPiece_partial_sum (χ:E→ℝ) (N:ℕ) (x:E) :
    (∑n∈Finset.range N,nativeCollarDyadicPiece χ (Real.exp ((n:ℝ)/4) • x))=
      χ x-nativeCollarDyadicCutoff χ N x := by
  induction N with
  | zero=>simp [nativeCollarDyadicCutoff]
  | succ N ih=>
    rw [Finset.sum_range_succ,ih,nativeCollarDyadicPiece_scale]
    ring

theorem nativeCollarDyadicCutoff_eventually_zero {χ:E→ℝ}
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ))) {x:E} (hx:x≠0) :
    ∀ᶠn:ℕ in atTop,nativeCollarDyadicCutoff χ n x=0 := by
  have hn:0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨N,hN⟩:=exists_nat_gt (4*((1/8:ℝ)-Real.log ‖x‖))
  filter_upwards [eventually_ge_atTop N] with n hNn
  change χ (Real.exp ((n:ℝ)/4) • x)=0
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have hb:=mem_ball_zero_iff.mp (hs hm)
  change ‖Real.exp ((n:ℝ)/4) • x‖ < Real.exp (1/8:ℝ) at hb
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hb
  have hnN:(N:ℝ) ≤ n := by exact_mod_cast hNn
  have he:Real.exp (1/8:ℝ) < Real.exp ((n:ℝ)/4)*‖x‖ := by
    rw [←Real.exp_log hn,←Real.exp_add]
    exact Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem nativeCollarDyadicPiece_tendsto_sum {χ:E→ℝ}
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ))) {x:E} (hx:x≠0) :
    Tendsto (fun N:ℕ=>∑n∈Finset.range N,nativeCollarDyadicPiece χ (Real.exp ((n:ℝ)/4) • x))
      atTop (𝓝 (χ x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [nativeCollarDyadicCutoff_eventually_zero hs hx] with N hN
  rw [nativeCollarDyadicPiece_partial_sum,hN,sub_zero]

#print axioms nativeCollarDyadicPiece_support
#print axioms nativeCollarDyadicPiece_partial_sum
#print axioms nativeCollarDyadicCutoff_eventually_zero
#print axioms nativeCollarDyadicPiece_tendsto_sum
end Yamabe3.Analysis.SpherePolar
