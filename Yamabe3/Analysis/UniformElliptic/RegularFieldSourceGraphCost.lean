import Yamabe3.Analysis.UniformElliptic.RegularFieldSourceGraph
import Yamabe3.Analysis.UniformElliptic.LocalProfileWeakNormComparison
import Yamabe3.Analysis.UniformElliptic.UniformProfileBound
import Yamabe3.Analysis.Cylinder.NativeCylinderPullback

/-! An actual original weighted H2 source graph from one regular field.
The sqrt(radius) normalization is retained; no weighted H4 decay of the
regular field is assumed. This is a source factory, not a PDE inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "E3" => EuclideanSpace ℝ (Fin 3)

def regularFieldSourceGraphCost : ℝ := max (Real.exp (Real.log 3/2))
  (((∑ j∈Finset.range (2+1),(Fintype.card (Fin j→Fin 3):ℝ≥0∞))*3*8*
    (volume halfEndSourceAnnulus)^(1/2:ℝ)).toReal)

theorem regularFieldSourceGraphCost_nonneg : 0≤regularFieldSourceGraphCost :=
  (Real.exp_pos _).le.trans (le_max_left _ _)

theorem exists_regularField_source_graph_with_cost (P : X →ₗ[ℝ] (E3→ℝ))
    (hP : ∀W,ContDiffOn ℝ ∞ (P W) (ball (0:E3) 5))
    (C : ℝ) (hC : 0≤C)
    (hb : ∀W,∀j≤2,∀x∈closedBall (0:E3) 4,‖iteratedFDeriv ℝ j (P W) x‖≤C*‖W‖) :
    ∃T : X →L[ℝ] HalfEndPhysicalH2SourceGraph,
      ‖T‖≤regularFieldSourceGraphCost*C ∧ ∀W,∀y : HalfEndSourceEntrance,
        halfEndPhysicalH2SourceGraphValue (T W) y=regularFieldSourceValue P W y := by
  have hcont W : Continuous (regularFieldSourceValue P W) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hn : 0<‖(y:E3)‖ := norm_pos_iff.mpr y.2.1
    have hy : (y:E3)∈ball (0:E3) 5 := by rw [mem_ball_zero_iff];linarith [y.2.2]
    exact (((Real.continuous_exp.continuousAt.comp
      ((Real.continuousAt_log (ne_of_gt hn)).comp continuous_norm.continuousAt |>.neg.div_const 2)).inv₀
        (radialScale_pos _).ne').comp continuous_subtype_val.continuousAt).mul
      ((hP W).continuousOn.continuousAt (isOpen_ball.mem_nhds hy) |>.comp continuous_subtype_val.continuousAt)
  let A := Real.exp (Real.log 3/2)
  have hA : 0≤A := (Real.exp_pos _).le
  have hv W (y : HalfEndSourceEntrance) : |regularFieldSourceValue P W y|≤(A*C)*‖W‖ := by
    have hn : 0<‖(y:E3)‖ := norm_pos_iff.mpr y.2.1
    have hi : |(radialScale ‖(y:E3)‖)⁻¹|≤A := by
      rw [abs_of_pos (inv_pos.mpr (radialScale_pos _))]
      change (Real.exp (-Real.log ‖(y:E3)‖/2))⁻¹≤_
      rw [←Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have hh := Real.log_le_log hn y.2.2
      linarith
    have hval : |P W y|≤C*‖W‖ := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
        hb W 0 (by norm_num) y (by rw [mem_closedBall,dist_zero_right];linarith [y.2.2])
    rw [regularFieldSourceValue,abs_mul]
    exact (mul_le_mul hi hval (abs_nonneg _) hA).trans_eq (by ring)
  let value (W:X) : HalfEndSourceValue := BoundedContinuousFunction.ofNormedAddCommGroup
    (regularFieldSourceValue P W) (hcont W) ((A*C)*‖W‖) (hv W)
  have hrow W (i : HalfEndPhysicalSliceIndex) : halfEndWeightedSourceSliceMap (value W) i
      =ᵐ[volume.restrict halfEndSourceAnnulus]
        (fun x => Real.exp (-i.1/2)*P W (Real.exp (-i.1) • x)) := by
    filter_upwards [ae_restrict_mem halfEndSourceAnnulus_isOpen.measurableSet] with x hx
    have hn : 0<‖x‖ := by linarith [hx.1]
    rw [halfEndWeightedSourceSliceMap_apply_in_ball (value W) i (norm_pos_iff.mp hn) hx.2.le]
    change radialScale ‖x‖*((radialScale ‖Real.exp (-i.1) • x‖)⁻¹*P W (Real.exp (-i.1) • x))=_
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,radialScale_mul_positive (Real.exp_pos _) hn,
      radialScale_exp_neg]
    have hid : radialScale ‖x‖*(Real.exp (i.1/2)*radialScale ‖x‖)⁻¹=Real.exp (-i.1/2) := by
      rw [mul_inv_rev]
      calc
        _ = (radialScale ‖x‖*(radialScale ‖x‖)⁻¹)*(Real.exp (i.1/2))⁻¹ := by ring
        _ = _ := by
          rw [mul_inv_cancel₀ (radialScale_pos _).ne',one_mul,←Real.exp_neg]
          congr 1
          ring
    exact (show radialScale ‖x‖*((Real.exp (i.1/2)*radialScale ‖x‖)⁻¹*P W (Real.exp (-i.1) • x))=
      (radialScale ‖x‖*(Real.exp (i.1/2)*radialScale ‖x‖)⁻¹)*P W (Real.exp (-i.1) • x) by ring).trans
        (congrArg (fun d:ℝ => d*P W (Real.exp (-i.1) • x)) hid)
  let N : ℝ≥0∞ := ∑ j∈Finset.range (2+1),(Fintype.card (Fin j→Fin 3):ℝ≥0∞)
  let H : ℝ≥0∞ := N*3*8*(volume halfEndSourceAnnulus)^(1/2:ℝ)
  have hvol : volume halfEndSourceAnnulus≠⊤ :=
    (measure_mono (show halfEndSourceAnnulus⊆closedBall (0:E3) 2 from fun x hx => by
      rw [mem_closedBall,dist_zero_right];linarith [hx.2])).trans_lt
        (isCompact_closedBall (0:E3) 2).measure_lt_top |>.ne
  have hH : H≠⊤ := by
    apply ENNReal.mul_ne_top
    · norm_num [N,Finset.sum_range_succ]
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol
  have hrows W i : MemWkp 2 2 (halfEndWeightedSourceSliceMap (value W) i) halfEndSourceAnnulus ∧
      (iteratedWeakSobolevNorm 2 2 (halfEndWeightedSourceSliceMap (value W) i) halfEndSourceAnnulus).toReal≤
        (H.toReal*C)*‖W‖ := by
    let r := Real.exp (-i.1)
    let k := Real.exp (-i.1/2)
    let S : E3→ℝ := fun x => k*P W (r • x)
    have hr : 0<r := Real.exp_pos _
    have hr2 : r≤2 := by
      dsimp only [r]
      calc Real.exp (-i.1)≤Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith [i.2])
           _ = 2 := Real.exp_log (by norm_num)
    have hk : 0≤k := (Real.exp_pos _).le
    have hk2 : k≤2 := by
      dsimp only [k]
      calc Real.exp (-i.1/2)≤Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith [i.2,Real.log_nonneg (by norm_num:(1:ℝ)≤2)])
           _ = 2 := Real.exp_log (by norm_num)
    have hmap : MapsTo (fun x:E3 => r • x) halfEndBasicAnnulus (ball (0:E3) 5) := by
      intro x hx
      rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg hr.le]
      have hh := mul_le_mul_of_nonneg_right hr2 (norm_nonneg x)
      linarith [hx.2]
    have hSs : ContDiffOn ℝ ∞ S halfEndBasicAnnulus :=
      contDiffOn_const.mul ((hP W).comp (contDiff_id.const_smul r).contDiffOn hmap)
    have hjets : ∀j≤2,∀x∈halfEndSourceAnnulus,‖iteratedFDeriv ℝ j S x‖≤8*(C*‖W‖) := by
      intro j hj x hx
      have hy : r • x∈closedBall (0:E3) 4 := by
        rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hr.le]
        nlinarith [mul_le_mul_of_nonneg_right hr2 (norm_nonneg x),hx.2]
      obtain ⟨v,hvS,_,hve⟩ := exists_smooth_compact_extension_near_compact isOpen_ball
        (isCompact_closedBall (0:E3) 4) (closedBall_subset_ball (by norm_num)) (hP W)
      have he : S =ᶠ[𝓝 x] (fun z => k*v (r • z)) := by
        have hh := (hve (r • x) hy).comp_tendsto (continuous_id.const_smul r).continuousAt
        filter_upwards [hh] with z hz
        change k*P W (r • z)=k*v (r • z)
        change v (r • z)=P W (r • z) at hz
        rw [hz]
      rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
      change ‖iteratedFDeriv ℝ j (fun z => k • v (r • z)) x‖≤_
      rw [iteratedFDeriv_const_smul_apply']
      · rw [norm_smul,Real.norm_of_nonneg hk,
          iteratedFDeriv_comp_const_smul r (hvS.of_le (by exact_mod_cast le_top)),norm_smul,norm_pow,Real.norm_of_nonneg hr.le,
          (hve (r • x) hy).iteratedFDeriv ℝ j |>.self_of_nhds]
        have hp : r^j≤4 := (pow_le_pow_left₀ hr.le hr2 j).trans
          ((pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) hj).trans_eq (by norm_num))
        exact (mul_le_mul hk2 (mul_le_mul hp (hb W j hj _ hy) (norm_nonneg _) (by norm_num))
          (by positivity) (by norm_num)).trans_eq (by ring)
      · exact ((hvS.comp (contDiff_id.const_smul r)).of_le (by exact_mod_cast le_top)).contDiffAt
    have hmem := memWk2_of_local_smooth halfEndSourceAnnulus_isOpen
      NativeJacobianAnnulus.sourceAnnulus_precompact halfEndBasicAnnulus_isOpen
      NativeJacobianAnnulus.closure_sourceAnnulus_subset_outer hSs 2
    refine ⟨(MemWkp_congr_ae (by norm_num) halfEndSourceAnnulus_isOpen (hrow W i)).mpr hmem,?_⟩
    rw [wkpNorm_congr_ae (k:=2) (by norm_num) halfEndSourceAnnulus_isOpen (hrow W i)]
    have hh := (actual_weak_norm_le_local_profile halfEndSourceAnnulus_isOpen
      NativeJacobianAnnulus.sourceAnnulus_precompact halfEndBasicAnnulus_isOpen
      NativeJacobianAnnulus.closure_sourceAnnulus_subset_outer hSs 2).trans
      (mul_le_mul le_rfl (derivativeProfile_le_of_jet_bound halfEndSourceAnnulus_isOpen.measurableSet
        2 (by positivity) hjets) zero_le zero_le)
    have hid : N*((2+1:ℝ≥0∞)*ENNReal.ofReal (8*(C*‖W‖))*(volume halfEndSourceAnnulus)^(1/2:ℝ))=
        H*ENNReal.ofReal C*ENNReal.ofReal ‖W‖ := by
      dsimp only [H]
      rw [ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤8),ENNReal.ofReal_mul hC]
      norm_num
      ring
    change iteratedWeakSobolevNorm 2 2 S halfEndSourceAnnulus≤
      N*((2+1:ℝ≥0∞)*ENNReal.ofReal (8*(C*‖W‖))*(volume halfEndSourceAnnulus)^(1/2:ℝ)) at hh
    rw [hid] at hh
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hH ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) hh
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC,ENNReal.toReal_ofReal (norm_nonneg W)] using ht
  let S W : HalfEndPhysicalH2SourceGraph := weakSobolevGraphOfBound _ _ _ _ (value W)
    (fun i => (hrows W i).1) ((H.toReal*C)*‖W‖) (fun i => (hrows W i).2)
  let D := max A H.toReal
  have hD : 0≤D := hA.trans (le_max_left _ _)
  have hSnorm W : ‖S W‖≤(D*C)*‖W‖ := by
    apply (weakSobolevGraphOfBound_norm_le _ _ _ _ _ _ _ (by positivity) _).trans
    apply max_le
    · exact ((BoundedContinuousFunction.norm_le (by positivity)).mpr (hv W)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hC) (norm_nonneg W))
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hC) (norm_nonneg W)
  let L : X →ₗ[ℝ] HalfEndPhysicalH2SourceGraph :=
    { toFun := S
      map_add' := by
        intro W Z
        apply halfEndPhysicalH2SourceGraphValue_injective
        ext y
        change regularFieldSourceValue P (W+Z) y=regularFieldSourceValue P W y+regularFieldSourceValue P Z y
        simp only [regularFieldSourceValue,map_add,Pi.add_apply,mul_add]
      map_smul' := by
        intro c W
        apply halfEndPhysicalH2SourceGraphValue_injective
        ext y
        change regularFieldSourceValue P (c • W) y=c*regularFieldSourceValue P W y
        simp only [regularFieldSourceValue,map_smul,Pi.smul_apply,smul_eq_mul]
        ring }
  exact ⟨L.mkContinuous (D*C) hSnorm,
    LinearMap.mkContinuous_norm_le _ (mul_nonneg hD hC) hSnorm,fun W y => rfl⟩

#print axioms regularFieldSourceGraphCost_nonneg
#print axioms exists_regularField_source_graph_with_cost
end Yamabe3.Analysis.UniformElliptic
