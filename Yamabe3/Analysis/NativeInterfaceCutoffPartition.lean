import Yamabe3.Analysis.NativeCollarDyadicPartition

/-! A compact interface piece and finitely many strictly exterior
collars complement the actual infinite inner energy partition. These
are identities of the same physical function, with no pointwise trace
assigned to an L2 representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar

def nativeInterfaceCutoff (χ:E→ℝ):E→ℝ := fun x=>χ (Real.exp (-(1/4:ℝ)) • x)-χ (Real.exp (1/4:ℝ) • x)
def nativeOuterCollarCutoff (χ:E→ℝ) (n:ℕ):E→ℝ := fun x=>χ (Real.exp (-(n:ℝ)/4) • x)

theorem nativeInterfaceCutoff_smooth {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (nativeInterfaceCutoff χ) :=
  (hχ.comp (contDiff_id.const_smul _)).sub (hχ.comp (contDiff_id.const_smul _))

theorem nativeInterfaceCutoff_compact {χ:E→ℝ} (hc:HasCompactSupport χ) :
    HasCompactSupport (nativeInterfaceCutoff χ) :=
  (hc.comp_homeomorph (Homeomorph.smulOfNeZero (Real.exp (-(1/4:ℝ))) (Real.exp_ne_zero _))).sub
    (hc.comp_homeomorph (Homeomorph.smulOfNeZero (Real.exp (1/4:ℝ)) (Real.exp_ne_zero _)))

theorem nativeInterfaceCutoff_support {χ:E→ℝ}
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1)) :
    tsupport (nativeInterfaceCutoff χ)⊆nativePoissonEntranceCollar := by
  intro x hx
  have hlow:Real.exp (-(3/8:ℝ)) < ‖x‖ := by
    by_contra hh
    have hn:‖x‖ ≤ Real.exp (-(3/8:ℝ)) := le_of_not_gt hh
    have hm (s:ℝ) (hs':s ≤ 1/4):Real.exp s • x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))) := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
      apply (mul_le_mul (Real.exp_le_exp.mpr hs') hn (norm_nonneg _) (Real.exp_pos _).le).trans_eq
      rw [←Real.exp_add]
      norm_num
    have he1:(fun y:E=>χ (Real.exp (-(1/4:ℝ)) • y))=ᶠ[𝓝 x](fun _=>1) :=
      (continuous_const_smul _).continuousAt.tendsto.eventually (h1 _ (hm _ (by norm_num)))
    have he2:(fun y:E=>χ (Real.exp (1/4:ℝ) • y))=ᶠ[𝓝 x](fun _=>1) :=
      (continuous_const_smul _).continuousAt.tendsto.eventually (h1 _ (hm _ le_rfl))
    have hz:nativeInterfaceCutoff χ=ᶠ[𝓝 x](fun _=>0) := by
      filter_upwards [he1,he2] with y h1 h2
      change χ (Real.exp (-(1/4:ℝ)) • y)-χ (Real.exp (1/4:ℝ) • y)=0
      rw [h1,h2,sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  have hu:‖x‖ < Real.exp (3/8:ℝ) := by
    by_contra hh
    have hn:Real.exp (3/8:ℝ) ≤ ‖x‖ := le_of_not_gt hh
    have hm (s:ℝ) (hs':-(1/4:ℝ) ≤ s):Real.exp s • x∉tsupport χ := by
      intro ht
      have hb:=mem_ball_zero_iff.mp (hs ht)
      rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hb
      have hh:Real.exp (1/8:ℝ) ≤ Real.exp s*‖x‖ := by
        calc
          _=Real.exp (-(1/4:ℝ))*Real.exp (3/8:ℝ) := by rw [←Real.exp_add];norm_num
          _ ≤ _ := mul_le_mul (Real.exp_le_exp.mpr hs') hn (Real.exp_pos _).le (Real.exp_pos _).le
      linarith
    have he1:(fun y:E=>χ (Real.exp (-(1/4:ℝ)) • y))=ᶠ[𝓝 x](fun _=>0) :=
      (continuous_const_smul _).continuousAt.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp (hm _ le_rfl))
    have he2:(fun y:E=>χ (Real.exp (1/4:ℝ) • y))=ᶠ[𝓝 x](fun _=>0) :=
      (continuous_const_smul _).continuousAt.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp (hm _ (by norm_num)))
    have hz:nativeInterfaceCutoff χ=ᶠ[𝓝 x](fun _=>0) := by
      filter_upwards [he1,he2] with y h1 h2
      change χ (Real.exp (-(1/4:ℝ)) • y)-χ (Real.exp (1/4:ℝ) • y)=0
      rw [h1,h2,sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx
  exact (nativePolarTimeWindow_norm (1/2) x).mpr
    ⟨(Real.exp_lt_exp.mpr (by norm_num:-(1/2:ℝ) < -(3/8:ℝ))).trans hlow,
      hu.trans (Real.exp_lt_exp.mpr (by norm_num:(3/8:ℝ) < 1/2))⟩

theorem nativeOuterCollarPiece_scale (χ:E→ℝ) (n:ℕ) (x:E) :
    nativeCollarDyadicPiece χ (Real.exp (-((n+1:ℕ):ℝ)/4) • x)=
      nativeOuterCollarCutoff χ (n+1) x-nativeOuterCollarCutoff χ n x := by
  dsimp only [nativeCollarDyadicPiece,nativeOuterCollarCutoff]
  rw [smul_smul,←Real.exp_add]
  congr 3
  push_cast
  ring

theorem nativeOuterCollarPiece_partial_sum (χ:E→ℝ) (N:ℕ) (x:E) :
    (∑n∈Finset.range N,nativeCollarDyadicPiece χ (Real.exp (-((n+2:ℕ):ℝ)/4) • x))=
      nativeOuterCollarCutoff χ (N+1) x-nativeOuterCollarCutoff χ 1 x := by
  induction N with
  | zero=>simp
  | succ N ih=>
    rw [Finset.sum_range_succ,ih]
    rw [show N+2=(N+1)+1 by omega,nativeOuterCollarPiece_scale]
    ring

theorem nativeOuterCollarPiece_zero_on_closed_unit {δ:E→ℝ}
    (hδ:tsupport δ⊆nativePoissonEntranceCollar) {s:ℝ} (hs:s ≤ -(1/2:ℝ))
    {x:E} (hx:‖x‖ ≤ 1) : δ (Real.exp s • x)=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hh:=((nativePolarTimeWindow_norm (1/2) (Real.exp s • x)).mp (hδ ht)).1
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hh
  have hb:Real.exp s*‖x‖ ≤ Real.exp (-(1/2:ℝ)) := by
    calc
      _ ≤ Real.exp s*1 := mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
      _ ≤ _ := by simpa only [mul_one] using Real.exp_le_exp.mpr hs
  linarith

theorem nativeInnerCutoff_zero_outside_unit {χ:E→ℝ}
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ))) {x:E} (hx:x∉ball (0:E) 1) :
    nativeCollarDyadicCutoff χ 1 x=0 := by
  simp only [nativeCollarDyadicCutoff,Nat.cast_one]
  change χ (Real.exp (1/4:ℝ) • x)=0
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hh:=mem_ball_zero_iff.mp (hs ht)
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hh
  have hn:1 ≤ ‖x‖ := le_of_not_gt (fun h=>hx (mem_ball_zero_iff.mpr h))
  have he:Real.exp (1/8:ℝ) < Real.exp (1/4:ℝ) := Real.exp_lt_exp.mpr (by norm_num)
  have hb:Real.exp (1/4:ℝ) ≤ Real.exp (1/4:ℝ)*‖x‖ := by nlinarith [Real.exp_pos (1/4:ℝ)]
  linarith

theorem nativeMatchedField_partition_identity {χ:E→ℝ}
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    (N:ℕ) (u v:E→ℝ) (x:E) :
    nativeCollarDyadicCutoff χ 1 x*u x+
      nativeInterfaceCutoff χ x*(ball (0:E) 1).piecewise u v x+
      (∑n∈Finset.range N,nativeCollarDyadicPiece χ (Real.exp (-((n+2:ℕ):ℝ)/4) • x)*v x)=
        nativeOuterCollarCutoff χ (N+1) x*(ball (0:E) 1).piecewise u v x := by
  classical
  have hi:nativeInterfaceCutoff χ x=nativeOuterCollarCutoff χ 1 x-nativeCollarDyadicCutoff χ 1 x := by
    norm_num [nativeInterfaceCutoff,nativeOuterCollarCutoff,nativeCollarDyadicCutoff]
  rw [←Finset.sum_mul,nativeOuterCollarPiece_partial_sum,hi]
  by_cases hx:x∈ball (0:E) 1
  · have hn:‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
    have hz:(∑n∈Finset.range N,nativeCollarDyadicPiece χ (Real.exp (-((n+2:ℕ):ℝ)/4) • x))=0 := by
      apply Finset.sum_eq_zero
      intro n _
      apply nativeOuterCollarPiece_zero_on_closed_unit (nativeCollarDyadicPiece_support hs h1) _ hn
      have hn':0 ≤ (n:ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
    rw [nativeOuterCollarPiece_partial_sum] at hz
    rw [piecewise_eq_of_mem _ _ _ hx]
    rw [hz,zero_mul]
    have he:nativeOuterCollarCutoff χ (N+1) x=nativeOuterCollarCutoff χ 1 x := sub_eq_zero.mp hz
    rw [he]
    ring
  · rw [nativeInnerCutoff_zero_outside_unit hs hx,piecewise_eq_of_notMem _ _ _ hx]
    ring

#print axioms nativeInterfaceCutoff_support
#print axioms nativeOuterCollarPiece_partial_sum
#print axioms nativeOuterCollarPiece_zero_on_closed_unit
#print axioms nativeMatchedField_partition_identity
end Yamabe3.Analysis.SpherePolar
