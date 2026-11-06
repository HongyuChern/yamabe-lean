import Yamabe3.Analysis.WeightedTaylorH4Profile
import Yamabe3.Analysis.UniformElliptic.LocalProfileWeakNormComparison
import Yamabe3.Analysis.UniformElliptic.HalfEndPhysicalH4Graph

/-! Actual graph membership of a smooth zero-first-jet field, with all
costs explicit in its Hessian and its genuine H4 L2 profile. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.Euclidean
local notation "E3" => EuclideanSpace ℝ (Fin 3)

def zeroFirstJetH4GraphCost (A B:ℝ) : ℝ :=
  max (16*A) (605*(8*A*((volume halfEndBasicAnnulus)^(1/2:ℝ)).toReal+2*B))

theorem exists_zeroFirstJetH4Graph
    {f:E3→ℝ} (hf:ContDiff ℝ ∞ f) (hf0:f 0=0) (hdf0:fderiv ℝ f 0=0)
    {A B:ℝ} (hA:0≤A) (hB:0≤B)
    (hsecond:∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ 2 f x‖≤A)
    (hprofile:derivativeProfile 2 (ball (0:E3) 4) 4 f≤ENNReal.ofReal B) :
    ∃v:HalfEndPhysicalH4Graph,
      (∀x:HalfEndEntranceBall,halfEndPhysicalH4GraphValue v x=f x) ∧
      ‖v‖≤zeroFirstJetH4GraphCost A B := by
  let value:HalfEndEntranceValue := ⟨fun x => f x,hf.continuous.comp continuous_subtype_val⟩
  have hval (y:HalfEndEntranceBall):‖value y‖≤16*A := by
    change ‖f y‖≤16*A
    have hy:‖(y:E3)‖≤4 := by simpa only [mem_closedBall,dist_zero_right] using y.2
    have hh:=zero_first_jet_quadratic_scaled_low_jets hf hf0 hdf0 hA hsecond
      2 (by norm_num) (by norm_num) 0 (by norm_num) ((1/2:ℝ) • (y:E3))
      (by rw [mem_closedBall,dist_zero_right,norm_smul];norm_num;linarith)
    simpa only [norm_iteratedFDeriv_zero,smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul,
      show 4*A*(2:ℝ)^2=16*A by ring] using hh
  have hcompact:IsCompact (closure halfEndBasicAnnulus) := by
    apply (isCompact_closedBall (0:E3) 2).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    rw [mem_closedBall,dist_zero_right]
    exact hx.2.le
  have hvol:volume halfEndBasicAnnulus≠⊤ :=
    (measure_mono (subset_closure)).trans_lt hcompact.measure_lt_top |>.ne
  let H:ℝ≥0∞ := 605*(ENNReal.ofReal (8*A)*(volume halfEndBasicAnnulus)^(1/2:ℝ)+2*ENNReal.ofReal B)
  have hH:H≠⊤ := by
    apply ENNReal.mul_ne_top (by norm_num)
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol),
      ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩
  have hrow i:halfEndWeightedPhysicalSliceMap value i=ᵐ[volume.restrict halfEndBasicAnnulus]
      weightedPhysicalDilation i.1 f := by
    filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
    exact halfEndWeightedPhysicalSliceMap_apply_in_ball value i hx.2.le
  have hsmooth s:ContDiffOn ℝ ∞ (weightedPhysicalDilation s f) univ :=
    ((contDiff_const.mul (hf.comp (contDiff_id.const_smul _))):ContDiff ℝ ∞ _).contDiffOn
  have hmem i:MemWkp 4 2 (halfEndWeightedPhysicalSliceMap value i) halfEndBasicAnnulus :=
    (MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen (hrow i)).mpr
      (memWk2_of_local_smooth halfEndBasicAnnulus_isOpen hcompact isOpen_univ (subset_univ _)
        (hsmooth i.1) 4)
  have hnorm i:(iteratedWeakSobolevNorm 4 2 (halfEndWeightedPhysicalSliceMap value i)
      halfEndBasicAnnulus).toReal≤H.toReal := by
    rw [wkpNorm_congr_ae (k:=4) (by norm_num) halfEndBasicAnnulus_isOpen (hrow i)]
    apply ENNReal.toReal_mono hH
    apply (actual_weak_norm_le_local_profile halfEndBasicAnnulus_isOpen hcompact isOpen_univ
      (subset_univ _) (hsmooth i.1) 4).trans
    have hh:derivativeProfile 2 halfEndBasicAnnulus 4 (weightedPhysicalDilation i.1 f)≤
        5*(ENNReal.ofReal (8*A)*(volume halfEndBasicAnnulus)^(1/2:ℝ)+2*ENNReal.ofReal B) :=
      (weightedPhysicalDilation_zero_jet_H4_profile hf hf0 hdf0 hA hsecond i.2).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprofile zero_le)) zero_le)
    apply (mul_le_mul_of_nonneg_left hh zero_le).trans_eq
    norm_num only [Finset.sum_range_succ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,
      Nat.cast_ofNat,pow_zero,pow_one,Finset.sum_range_zero,zero_add] 
    dsimp only [H]
    ring
  let v:HalfEndPhysicalH4Graph := weakSobolevGraphOfBound _ _ _ _ value hmem H.toReal hnorm
  refine ⟨v,fun x => rfl,?_⟩
  apply (weakSobolevGraphOfBound_norm_le _ _ _ _ _ _ _ ENNReal.toReal_nonneg _).trans
  apply max_le_max
  · exact (ContinuousMap.norm_le value (by positivity)).mpr hval
  · dsimp only [H]
    rw [ENNReal.toReal_mul,ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol))
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity:0≤8*A),
      ENNReal.toReal_ofReal hB]
    norm_num only [ENNReal.toReal_ofNat]
    exact le_rfl

#print axioms exists_zeroFirstJetH4Graph
end Yamabe3.Analysis.UniformElliptic
