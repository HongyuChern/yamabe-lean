import Yamabe3.Analysis.WeightedDilationProfileTools
import Yamabe3.Analysis.UniformElliptic.TaylorRemainderBounds
import Yamabe3.Analysis.UniformElliptic.UniformProfileBound

/-! The critical H4 rows of the SAME first Taylor remainder.
High orders use actual L2 change of variables, not a new pointwise H4
hypothesis. Low orders use only the true Hessian bound and zero first jet. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem weightedPhysicalDilation_high_term_le
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) {s:ℝ} (hs : -(Real.log 2) ≤ s)
    {n:ℕ} (hn3:3≤n) (hn4:n≤4) :
    eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ n (weightedPhysicalDilation s f) x‖) 2
      (volume.restrict halfEndBasicAnnulus) ≤
        2*eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ n f x‖) 2
          (volume.restrict (ball (0:E3) 4)) := by
  have hr2:Real.exp (-s)≤2 := by
    calc Real.exp (-s)≤Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
         _ = 2 := Real.exp_log (by norm_num)
  have hsub:halfEndBasicAnnulus⊆(fun x:E3 => Real.exp (-s) • x) ⁻¹' ball (0:E3) 4 := by
    intro x hx
    rw [mem_preimage,mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_right hr2 (norm_nonneg x)).trans_lt (by linarith [hx.2])
  have hcoeff:(Real.exp (3*s/2)*Real.exp (-s)^n)*Real.exp (3*s/2)≤2 := by
    have he:(Real.exp (3*s/2)*Real.exp (-s)^n)*Real.exp (3*s/2)=Real.exp ((3-(n:ℝ))*s) := by
      rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    rw [he]
    interval_cases n
    · norm_num
    · norm_num only [Nat.cast_ofNat,show (3:ℝ)-4= -1 by norm_num,neg_one_mul]
      exact hr2
  rw [weightedPhysicalDilation_profile_term hf]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (3*s/2)*Real.exp (-s)^n)*
        eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ n f (Real.exp (-s) • x)‖) 2
          (volume.restrict ((fun x:E3 => Real.exp (-s) • x) ⁻¹' ball (0:E3) 4)) :=
      mul_le_mul le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)) zero_le zero_le
    _ = (ENNReal.ofReal (Real.exp (3*s/2)*Real.exp (-s)^n)*
          ENNReal.ofReal (Real.exp (3*s/2)))*
        eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ n f x‖) 2
          (volume.restrict (ball (0:E3) 4)) := by
      rw [eLpNorm_comp_dilation (r:=Real.exp (-s)) (Real.exp_pos _).ne'
        (ball (0:E3) 4) (fun x:E3 => ‖iteratedFDeriv ℝ n f x‖),dilationL2Factor_three_exp,mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      rw [←ENNReal.ofReal_mul (by positivity)]
      exact (ENNReal.ofReal_le_ofReal hcoeff).trans_eq (by norm_num)

theorem weightedPhysicalDilation_low_jet_le
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) (hf0:f 0=0) (hdf0:fderiv ℝ f 0=0)
    {A:ℝ} (hA:0≤A)
    (hsecond:∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ 2 f x‖≤A)
    {s:ℝ} (hs : -(Real.log 2) ≤ s) {n:ℕ} (hn:n≤2)
    {x:E3} (hx:x∈halfEndBasicAnnulus) :
    ‖iteratedFDeriv ℝ n (weightedPhysicalDilation s f) x‖≤8*A := by
  have hr2:Real.exp (-s)≤2 := by
    calc Real.exp (-s)≤Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
         _ = 2 := Real.exp_log (by norm_num)
  have hhh:=zero_first_jet_quadratic_scaled_low_jets hf hf0 hdf0 hA hsecond
    (Real.exp (-s)) (Real.exp_pos _).le hr2 n hn x
    (by rw [mem_closedBall,dist_zero_right];exact hx.2.le)
  have hsm:ContDiffAt ℝ n (fun y:E3 => f (Real.exp (-s) • y)) x :=
    ((hf.comp (contDiff_id.const_smul _)).of_le (by exact_mod_cast le_top)).contDiffAt
  change ‖iteratedFDeriv ℝ n (Real.exp (3*s/2) • (fun y:E3 => f (Real.exp (-s) • y))) x‖≤_
  rw [iteratedFDeriv_const_smul_apply (a:=Real.exp (3*s/2)) hsm,
    norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left hhh (Real.exp_pos _).le).trans
  have he:Real.exp (3*s/2)*(4*A*Real.exp (-s)^2)=4*A*Real.exp (-s/2) := by
    rw [pow_two,←Real.exp_add]
    calc Real.exp (3*s/2)*(4*A*Real.exp (-s+-s))=
        4*A*(Real.exp (3*s/2)*Real.exp (-s+-s)) := by ring
         _ = _ := by rw [←Real.exp_add];congr 2;ring
  rw [he]
  have hhalf:Real.exp (-s/2)≤2 := by
    calc Real.exp (-s/2)≤Real.exp (Real.log 2) :=
           Real.exp_le_exp.mpr (by linarith [Real.log_nonneg (by norm_num:(1:ℝ)≤2)])
         _ = 2 := Real.exp_log (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0≤4*A by positivity)]

theorem weightedPhysicalDilation_zero_jet_H4_profile
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) (hf0:f 0=0) (hdf0:fderiv ℝ f 0=0)
    {A:ℝ} (hA:0≤A)
    (hsecond:∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ 2 f x‖≤A)
    {s:ℝ} (hs : -(Real.log 2) ≤ s) :
    derivativeProfile 2 halfEndBasicAnnulus 4 (weightedPhysicalDilation s f) ≤
      5*(ENNReal.ofReal (8*A)*(volume halfEndBasicAnnulus)^(1/2:ℝ)+
        2*derivativeProfile 2 (ball (0:E3) 4) 4 f) := by
  unfold derivativeProfile
  calc
    _ ≤ ∑ n∈Finset.range (4+1),
        (ENNReal.ofReal (8*A)*(volume halfEndBasicAnnulus)^(1/2:ℝ)+
          2*∑ j∈Finset.range (4+1),eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ j f x‖) 2
            (volume.restrict (ball (0:E3) 4))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn4:n≤4 := by have:=Finset.mem_range.mp hn;omega
      by_cases hn2:n≤2
      · apply le_add_of_le_left
        have hp:=eLpNorm_le_of_ae_bound (p:=2) (μ:=volume.restrict halfEndBasicAnnulus)
          (f:=fun x:E3 => ‖iteratedFDeriv ℝ n (weightedPhysicalDilation s f) x‖)
          (show ∀ᵐx∂volume.restrict halfEndBasicAnnulus,
            ‖‖iteratedFDeriv ℝ n (weightedPhysicalDilation s f) x‖‖≤8*A from by
              filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
              simpa only [norm_norm] using weightedPhysicalDilation_low_jet_le hf hf0 hdf0 hA hsecond hs hn2 hx)
        simpa only [Measure.restrict_apply_univ,ENNReal.toReal_ofNat,show (2:ℝ)⁻¹=(1/2:ℝ) by norm_num,mul_comm] using hp
      · apply (weightedPhysicalDilation_high_term_le hf hs (by omega) hn4).trans
        apply le_add_of_le_right
        apply mul_le_mul_of_nonneg_left _ zero_le
        exact Finset.single_le_sum (f:=fun j => eLpNorm (fun x:E3 => ‖iteratedFDeriv ℝ j f x‖) 2
          (volume.restrict (ball (0:E3) 4))) (fun _ _ => zero_le) hn
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];norm_num

#print axioms weightedPhysicalDilation_high_term_le
#print axioms weightedPhysicalDilation_low_jet_le
#print axioms weightedPhysicalDilation_zero_jet_H4_profile
end Yamabe3.Analysis.UniformElliptic
