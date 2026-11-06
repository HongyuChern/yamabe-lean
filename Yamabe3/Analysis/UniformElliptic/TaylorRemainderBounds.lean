import Yamabe3.Analysis.QuadraticDilatedJetDecay

/-! Uniform Taylor subtraction with the ACTUAL value and derivative.
Only the Hessian bound is used for orders zero and one. Higher jets of
the remainder are exactly those of the same original function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter Metric
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "E3" => EuclideanSpace ℝ (Fin 3)

def firstTaylorRemainder (f:E3→ℝ) (x:E3) : ℝ :=
  f x-f 0-fderiv ℝ f 0 x

theorem firstTaylorRemainder_smooth {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (firstTaylorRemainder f) :=
  (hf.sub contDiff_const).sub (fderiv ℝ f 0).contDiff

theorem firstTaylorRemainder_first_jet {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) :
    firstTaylorRemainder f 0=0 ∧ fderiv ℝ (firstTaylorRemainder f) 0=0 := by
  refine ⟨by simp [firstTaylorRemainder],?_⟩
  change fderiv ℝ (fun x:E3 => (f x-f 0)-(fderiv ℝ f 0) x) 0=0
  rw [fderiv_fun_sub ((hf.differentiable (by simp) 0).sub_const _) (fderiv ℝ f 0).differentiableAt,
    fderiv_sub_const,(fderiv ℝ f 0).fderiv,sub_self]

theorem firstTaylorRemainder_higher_jet {f:E3→ℝ} (hf:ContDiff ℝ ∞ f)
    {n:ℕ} (hn:2≤n) (x:E3) :
    iteratedFDeriv ℝ n (firstTaylorRemainder f) x=iteratedFDeriv ℝ n f x := by
  have hn0:n≠0 := by omega
  have hlinear:iteratedFDeriv ℝ n (fderiv ℝ f 0) x=0 := by
    apply norm_eq_zero.mp
    obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
    have hnm:n=(m+1)+1 := by omega
    rw [hnm,←norm_iteratedFDeriv_fderiv (n:=m+1)]
    have he:fderiv ℝ (fderiv ℝ f 0:E3→ℝ)=(fun _:E3 => fderiv ℝ f 0) := by
      funext y
      exact (fderiv ℝ f 0).fderiv
    rw [he,iteratedFDeriv_succ_const]
    simp
  unfold firstTaylorRemainder
  rw [fun_iteratedFDeriv_sub_apply
    ((hf.sub contDiff_const).contDiffAt.of_le (by exact_mod_cast le_top))
    ((fderiv ℝ f 0).contDiff.contDiffAt.of_le (by exact_mod_cast le_top)),hlinear,sub_zero,
    fun_iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne hn0,Pi.zero_apply,sub_zero]

theorem zero_first_jet_quadratic_scaled_low_jets
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) (hf0:f 0=0) (hdf0:fderiv ℝ f 0=0)
    {A:ℝ} (hA:0≤A)
    (hsecond:∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ 2 f x‖≤A) :
    ∀r:ℝ,0≤r → r≤2 → ∀n≤2,∀x∈closedBall (0:E3) 2,
      ‖iteratedFDeriv ℝ n (fun y => f (r • y)) x‖≤4*A*r^2 := by
  have hD (y:E3) (hy:y∈closedBall (0:E3) 4):‖fderiv ℝ f y‖≤A*‖y‖ := by
    have hdd (z:E3) (hz:z∈closedBall (0:E3) 4):‖fderiv ℝ (fderiv ℝ f) z‖≤A := by
      rw [←norm_iteratedFDeriv_one (fderiv ℝ f),norm_iteratedFDeriv_fderiv]
      exact hsecond z hz
    have h := (convex_closedBall (0:E3) 4).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.fderiv_right (m:=1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable (by norm_num) z)
      hdd (mem_closedBall_self (by norm_num)) hy
    simpa only [hdf0,sub_zero] using h
  have hval (y:E3) (hy:y∈closedBall (0:E3) 4):‖f y‖≤A*‖y‖^2 := by
    have hyn:‖y‖≤4 := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hgrad (z:E3) (hz:z∈closedBall (0:E3) ‖y‖):‖fderiv ℝ f z‖≤A*‖y‖ :=
      (hD z ((closedBall_subset_closedBall hyn) hz)).trans
        (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall,dist_zero_right] using hz) hA)
    have h := (convex_closedBall (0:E3) ‖y‖).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf.differentiable (by simp) z) hgrad
      (mem_closedBall_self (norm_nonneg _)) (show y∈closedBall (0:E3) ‖y‖ by simp)
    simpa only [hf0,sub_zero,mul_assoc,pow_two] using h
  intro r hr hr2 n hn x hx
  have hx2:‖x‖≤2 := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hy:r • x∈closedBall (0:E3) 4 := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hr]
    nlinarith [mul_le_mul hr2 hx2 (norm_nonneg _) (by norm_num)]
  interval_cases n
  · rw [norm_iteratedFDeriv_zero]
    apply (hval _ hy).trans
    rw [norm_smul,Real.norm_of_nonneg hr,mul_pow]
    have hx4:‖x‖^2≤4 := by nlinarith [norm_nonneg x]
    nlinarith [mul_le_mul_of_nonneg_left hx4 (mul_nonneg hA (sq_nonneg r))]
  · rw [iteratedFDeriv_comp_const_smul r (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)),
      norm_smul,norm_pow,Real.norm_of_nonneg hr,pow_one,norm_iteratedFDeriv_one]
    apply (mul_le_mul_of_nonneg_left (hD _ hy) hr).trans
    rw [norm_smul,Real.norm_of_nonneg hr]
    nlinarith [mul_le_mul_of_nonneg_left hx2 (mul_nonneg hA (sq_nonneg r))]
  · rw [iteratedFDeriv_comp_const_smul r (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      norm_smul,norm_pow,Real.norm_of_nonneg hr]
    apply (mul_le_mul_of_nonneg_left (hsecond _ hy) (sq_nonneg r)).trans
    nlinarith [mul_nonneg hA (sq_nonneg r)]

#print axioms firstTaylorRemainder_first_jet
#print axioms firstTaylorRemainder_higher_jet
#print axioms zero_first_jet_quadratic_scaled_low_jets
end Yamabe3.Analysis.UniformElliptic
