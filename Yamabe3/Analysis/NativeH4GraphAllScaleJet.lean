import Yamabe3.Analysis.NativeH4CollarRealization
import Yamabe3.Analysis.NativePrincipalErrorRows
import Yamabe3.Analysis.NativeCollarJetValueInjective

/-! Every retained weighted H4 slice produces the same actual value,
first and second weak jets on the collar. The resulting linear map has
norm at most one, uniformly in scale. No new independent jet is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Delaunay

def nativeH4GraphScaleJet (i : HalfEndPhysicalSliceIndex) (v : HalfEndPhysicalH4Graph) : nativeCollarJetClosure :=
  Classical.choose (exists_nativeCollarJet_of_weak_H4 (v.2 i).1)

theorem nativeH4GraphScaleJet_rep (i : HalfEndPhysicalSliceIndex) (v : HalfEndPhysicalH4Graph) :
    ((nativeH4GraphScaleJet i v).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      halfEndWeightedPhysicalSliceMap v.1.1 i :=
  (Classical.choose_spec (exists_nativeCollarJet_of_weak_H4 (v.2 i).1)).1

theorem nativeH4GraphScaleJet_norm (i : HalfEndPhysicalSliceIndex) (v : HalfEndPhysicalH4Graph) :
    ‖nativeH4GraphScaleJet i v‖≤‖v‖ := by
  have h := (Classical.choose_spec (exists_nativeCollarJet_of_weak_H4 (v.2 i).1)).2
  apply h.trans
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top (halfEndWeightedPhysicalSliceMap_norm_le v i)
  simpa only [ENNReal.toReal_ofReal (norm_nonneg v)] using hn

def nativeH4GraphScaleJetLinear (i : HalfEndPhysicalSliceIndex) : HalfEndPhysicalH4Graph →ₗ[ℝ] nativeCollarJetClosure where
  toFun := nativeH4GraphScaleJet i
  map_add' v w := by
    apply nativeCollarJet_value_injective
    apply Lp.ext
    filter_upwards [nativeH4GraphScaleJet_rep i (v+w),nativeH4GraphScaleJet_rep i v,nativeH4GraphScaleJet_rep i w,
      Lp.coeFn_add (nativeH4GraphScaleJet i v).val.1 (nativeH4GraphScaleJet i w).val.1] with x hs hv hw ha
    change (nativeH4GraphScaleJet i (v+w)).val.1 x=((nativeH4GraphScaleJet i v).val.1+(nativeH4GraphScaleJet i w).val.1 : NativeCollarL2) x
    rw [hs,ha]
    change _=(nativeH4GraphScaleJet i v).val.1 x+(nativeH4GraphScaleJet i w).val.1 x
    rw [hv,hw]
    change halfEndWeightedPhysicalSliceMap (v.1.1+w.1.1) i x= _
    rw [map_add]
    rfl
  map_smul' c v := by
    apply nativeCollarJet_value_injective
    apply Lp.ext
    filter_upwards [nativeH4GraphScaleJet_rep i (c•v),nativeH4GraphScaleJet_rep i v,
      Lp.coeFn_smul c (nativeH4GraphScaleJet i v).val.1] with x hs hv ha
    change (nativeH4GraphScaleJet i (c•v)).val.1 x=(c • (nativeH4GraphScaleJet i v).val.1 : NativeCollarL2) x
    rw [hs,ha]
    change _=c*(nativeH4GraphScaleJet i v).val.1 x
    rw [hv]
    change halfEndWeightedPhysicalSliceMap (c•v.1.1) i x= _
    rw [map_smul]
    rfl

def nativeH4GraphScaleJetCLM (i : HalfEndPhysicalSliceIndex) : HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure :=
  (nativeH4GraphScaleJetLinear i).mkContinuous 1 (fun v => by change ‖nativeH4GraphScaleJet i v‖≤1*‖v‖; simpa only [one_mul] using nativeH4GraphScaleJet_norm i v)

theorem nativeH4GraphScaleJetCLM_norm (i : HalfEndPhysicalSliceIndex) : ‖nativeH4GraphScaleJetCLM i‖≤1 :=
  (nativeH4GraphScaleJetCLM i).opNorm_le_bound (by norm_num) (fun v => by change ‖nativeH4GraphScaleJet i v‖≤1*‖v‖; simpa only [one_mul] using nativeH4GraphScaleJet_norm i v)

theorem nativeH4GraphScaleJet_same_function (i : HalfEndPhysicalSliceIndex) (v : HalfEndPhysicalH4Graph)
    (F : E→ℝ) (hF : EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) F (closedBall (0:E) 4)) :
    ((nativeH4GraphScaleJetCLM i v).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*i.1/2)*F (Real.exp (-i.1) • x)) := by
  filter_upwards [nativeH4GraphScaleJet_rep i v,
    ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hxO
  change (nativeH4GraphScaleJet i v).val.1 x=_
  rw [hx]
  change Real.exp (3*i.1/2)*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) (Real.exp (-i.1) • x)=_
  rw [hF (halfEnd_physical_slice_mem_entrance_ball i (nativeEntranceCollar_annular hxO).2)]

theorem nativeH4GraphScaleJet_zero_C2 (v : HalfEndPhysicalH4Graph) (u : nativeC2OffZero)
    (hu : EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4)) :
    nativeH4GraphScaleJetCLM ⟨0,neg_nonpos.mpr (Real.log_nonneg (by norm_num))⟩ v=nativeC2CollarJetInclusion u := by
  apply nativeCollarJet_value_injective
  apply Lp.ext
  have h := nativeH4GraphScaleJet_same_function ⟨0,neg_nonpos.mpr (Real.log_nonneg (by norm_num))⟩ v u.val hu
  simp only [mul_zero,zero_div,Real.exp_zero,neg_zero,one_smul,one_mul] at h
  exact h.trans (nativeC2Collar_memLp u.property).1.coeFn_toLp.symm

#print axioms nativeH4GraphScaleJet_rep
#print axioms nativeH4GraphScaleJet_norm
#print axioms nativeH4GraphScaleJetCLM_norm
#print axioms nativeH4GraphScaleJet_same_function
#print axioms nativeH4GraphScaleJet_zero_C2
end Yamabe3.Analysis.UniformElliptic
