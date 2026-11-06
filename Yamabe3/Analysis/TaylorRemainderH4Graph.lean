import Yamabe3.Analysis.ZeroFirstJetH4Graph

/-! A genuine first Taylor subtraction lands in the weighted H4 graph.
The real low jets are retained; only a Hessian bound and the same H4
profile are used. No pointwise fourth derivative bound is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem zero_first_jet_low_jets_ball_four
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) (hf0:f 0=0) (hdf0:fderiv ℝ f 0=0)
    {A:ℝ} (hA:0≤A)
    (hsecond:∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ 2 f x‖≤A) :
    ∀n≤2,∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ n f x‖≤16*A := by
  intro n hn x hx
  have hnorm:‖x‖≤4 := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hh:=zero_first_jet_quadratic_scaled_low_jets hf hf0 hdf0 hA hsecond
    2 (by norm_num) (by norm_num) n hn ((1/2:ℝ) • x)
    (by rw [mem_closedBall,dist_zero_right,norm_smul];norm_num;linarith)
  rw [iteratedFDeriv_comp_const_smul 2 (hf.of_le (by exact_mod_cast le_top)),norm_smul,norm_pow,
    show ‖(2:ℝ)‖=2 by norm_num,smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] at hh
  have hp:(1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  exact (le_mul_of_one_le_left (norm_nonneg _) hp).trans (hh.trans_eq (by ring))

def firstTaylorRemainderProfileCost (A B:ℝ) : ℝ :=
  5*(16*A*((volume (ball (0:E3) 4))^(1/2:ℝ)).toReal+B)

theorem firstTaylorRemainder_profile_bound
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) {A B:ℝ} (hA:0≤A) (hB:0≤B)
    (hsecond:∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ 2 f x‖≤A)
    (hprofile:derivativeProfile 2 (ball (0:E3) 4) 4 f≤ENNReal.ofReal B) :
    derivativeProfile 2 (ball (0:E3) 4) 4 (firstTaylorRemainder f)≤
      ENNReal.ofReal (firstTaylorRemainderProfileCost A B) := by
  have hj:=firstTaylorRemainder_first_jet hf
  have hb:∀n≤2,∀x∈closedBall (0:E3) 4,
      ‖iteratedFDeriv ℝ n (firstTaylorRemainder f) x‖≤16*A :=
    zero_first_jet_low_jets_ball_four (firstTaylorRemainder_smooth hf) hj.1 hj.2 hA
      (fun x hx => by rw [firstTaylorRemainder_higher_jet hf (by norm_num:2≤2)];exact hsecond x hx)
  have hvol:volume (ball (0:E3) 4)≠⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0:E3) 4).measure_lt_top |>.ne
  have hv:((volume (ball (0:E3) 4))^(1/2:ℝ))≠⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol
  have hh:derivativeProfile 2 (ball (0:E3) 4) 4 (firstTaylorRemainder f)≤
      5*(ENNReal.ofReal (16*A)*(volume (ball (0:E3) 4))^(1/2:ℝ)+ENNReal.ofReal B) := by
    unfold derivativeProfile
    calc
      _ ≤ ∑ n∈Finset.range (4+1),
          (ENNReal.ofReal (16*A)*(volume (ball (0:E3) 4))^(1/2:ℝ)+ENNReal.ofReal B) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn2:n≤2
        · apply le_add_of_le_left
          have h:=eLpNorm_le_of_ae_bound (p:=2) (μ:=volume.restrict (ball (0:E3) 4))
            (f:=fun x:E3 => ‖iteratedFDeriv ℝ n (firstTaylorRemainder f) x‖)
            (show ∀ᵐx∂volume.restrict (ball (0:E3) 4),
              ‖‖iteratedFDeriv ℝ n (firstTaylorRemainder f) x‖‖≤16*A from by
              filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
              simpa only [norm_norm] using hb n hn2 x (ball_subset_closedBall hx))
          simpa only [Measure.restrict_apply_univ,ENNReal.toReal_ofNat,
            show (2:ℝ)⁻¹=(1/2:ℝ) by norm_num,mul_comm] using h
        · simp_rw [firstTaylorRemainder_higher_jet hf (by omega:2≤n)]
          apply le_add_of_le_right
          apply (Finset.single_le_sum (f:=fun j => eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ j f x‖) 2
            (volume.restrict (ball (0:E3) 4))) (fun _ _ => zero_le) hn).trans hprofile
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];norm_num
  apply hh.trans_eq
  rw [firstTaylorRemainderProfileCost,ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤5),
    ENNReal.ofReal_add (by positivity) hB,ENNReal.ofReal_mul (by positivity:0≤16*A),
    ENNReal.ofReal_toReal hv]
  norm_num

 theorem exists_firstTaylorRemainderH4Graph
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) {A B:ℝ} (hA:0≤A) (hB:0≤B)
    (hsecond:∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ 2 f x‖≤A)
    (hprofile:derivativeProfile 2 (ball (0:E3) 4) 4 f≤ENNReal.ofReal B) :
    ∃v:HalfEndPhysicalH4Graph,
      (∀x:HalfEndEntranceBall,halfEndPhysicalH4GraphValue v x=firstTaylorRemainder f x) ∧
      ‖v‖≤zeroFirstJetH4GraphCost A (firstTaylorRemainderProfileCost A B) := by
  have hj:=firstTaylorRemainder_first_jet hf
  exact exists_zeroFirstJetH4Graph (firstTaylorRemainder_smooth hf) hj.1 hj.2 hA
    (by unfold firstTaylorRemainderProfileCost;positivity)
    (fun x hx => by rw [firstTaylorRemainder_higher_jet hf (by norm_num:2≤2)];exact hsecond x hx)
    (firstTaylorRemainder_profile_bound hf hA hB hsecond hprofile)

#print axioms zero_first_jet_low_jets_ball_four
#print axioms firstTaylorRemainder_profile_bound
#print axioms exists_firstTaylorRemainderH4Graph
end Yamabe3.Analysis.UniformElliptic
