import Yamabe3.Analysis.NativeRegularH4PrincipalError
import Yamabe3.Analysis.WeightedH4FirstJetDecay
import Mathlib.Topology.TietzeExtension

/-! The low coordinates in the complete regular-plus-weighted space
are the ACTUAL value and first derivative of its one physical field.
A weighted H4 graph element cannot hide an affine term at the puncture.
The continuous extension used in the proof has no independent PDE role. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Sobolev.Euclidean
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem halfEndH4Graph_origin_jet (v:HalfEndPhysicalH4Graph) :
    halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) 0=0 ∧
    HasFDerivAt (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) (0:E3 →L[ℝ] ℝ) 0 := by
  let f := halfEndPhysicalH4GraphValue v
  obtain ⟨u,hu⟩ := ContinuousMap.exists_restrict_eq (isClosed_closedBall : IsClosed (closedBall (0:E3) 4)) f
  have heq {x:E3} (hx:x∈closedBall (0:E3) 4) : u x=halfEndEntranceExtension f x := by
    rw [halfEndEntranceExtension_of_mem f hx]
    exact congrArg (fun F:C(HalfEndEntranceBall,ℝ) => F ⟨x,hx⟩) hu
  have hall (s:ℝ) (hs : -Real.log 2 ≤ s) : MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
      iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus≤ENNReal.ofReal ‖v‖ := by
    let i:HalfEndPhysicalSliceIndex := ⟨s,hs⟩
    have hae : weightedPhysicalDilation s u=ᵐ[volume.restrict halfEndBasicAnnulus]
        halfEndWeightedPhysicalSliceMap v.val.1 i := by
      filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
      change Real.exp (3*s/2)*u (Real.exp (-s) • x)=
        Real.exp (3*s/2)*halfEndEntranceExtension f (Real.exp (-s) • x)
      rw [heq (halfEnd_physical_slice_mem_entrance_ball i hx.2.le)]
    refine ⟨(Poincare.Analysis.Sobolev.Euclidean.MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen hae).mpr (v.2 i).1,?_⟩
    rw [Poincare.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae (k:=4) (by norm_num) halfEndBasicAnnulus_isOpen hae]
    exact halfEndWeightedPhysicalSliceMap_norm_le v i
  obtain ⟨D,hD,hb⟩ := exists_weighted_H4_first_jet_decay_constant
  have hdec := hb u u.continuous.continuousOn (ENNReal.ofReal ‖v‖) ENNReal.ofReal_ne_top hall
  let C := D*(ENNReal.ofReal ‖v‖).toReal
  have hlim : Tendsto (fun x:E3 => C*‖x‖*Real.sqrt ‖x‖) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x:E3 => C*‖x‖*Real.sqrt ‖x‖) := by fun_prop
    convert! hc.tendsto (0:E3) using 1 <;> simp

  have hlimU : Tendsto u (𝓝[≠] (0:E3)) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:E3) zero_lt_one)] with x hx hx1
    exact (hdec x hx (by exact (show ‖x‖<1 from by simpa only [mem_ball_zero_iff] using hx1).le)).1
  have h0 : u 0=0 :=
    (tendsto_nhds_unique (u.continuous.tendsto (0:E3) |>.mono_left nhdsWithin_le_nhds) hlimU)
  have hrate : Tendsto (fun x:E3 => C*Real.sqrt ‖x‖) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x:E3 => C*Real.sqrt ‖x‖) := by fun_prop
    convert! hc.tendsto (0:E3) using 1 <;> simp

  have hn : Tendsto (fun x:E3 => ‖x‖⁻¹*‖u x‖) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun x => mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (norm_nonneg _)) ?_ hrate
    filter_upwards [Metric.ball_mem_nhds (0:E3) zero_lt_one] with x hx
    have hx1 : ‖x‖≤1 := (by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<1).le
    by_cases hx0:x=0
    · simp [hx0]
    · calc
        ‖x‖⁻¹*‖u x‖≤‖x‖⁻¹*(C*‖x‖*Real.sqrt ‖x‖) :=
          mul_le_mul_of_nonneg_left (hdec x hx0 hx1).1 (inv_nonneg.mpr (norm_nonneg x))
        _ = C*Real.sqrt ‖x‖ := by field_simp
  have hd : HasFDerivAt u (0:E3 →L[ℝ] ℝ) 0 := by
    rw [hasFDerivAt_iff_tendsto]
    simpa only [sub_zero,h0,ContinuousLinearMap.zero_apply] using hn
  have hge : halfEndEntranceExtension f=ᶠ[𝓝 (0:E3)] u := by
    filter_upwards [Metric.ball_mem_nhds (0:E3) (by norm_num:(0:ℝ)<4)] with x hx
    exact (heq (ball_subset_closedBall hx)).symm
  exact ⟨(heq (mem_closedBall_self (by norm_num))).symm.trans h0,hd.congr_of_eventuallyEq hge⟩

theorem regularLowH4Field_low_value (z:RegularLowH4Space) : regularLowH4Field z 0=z.1.1 := by
  simp only [regularLowH4Field,regularAffineField,map_zero,(halfEndH4Graph_origin_jet z.2).1,add_zero]

theorem regularLowH4Field_low_derivative (z:RegularLowH4Space) :
    HasFDerivAt (regularLowH4Field z) z.1.2 0 := by
  have ha : HasFDerivAt (regularAffineField z.1) z.1.2 (0:E3) := by
    convert! (hasFDerivAt_const z.1.1 (0:E3)).add z.1.2.hasFDerivAt using 1 <;> simp [regularAffineField]
  convert! ha.add (halfEndH4Graph_origin_jet z.2).2 using 1 <;> simp [regularLowH4Field]

#print axioms halfEndH4Graph_origin_jet
#print axioms regularLowH4Field_low_value
#print axioms regularLowH4Field_low_derivative
end Yamabe3.Analysis.UniformElliptic
