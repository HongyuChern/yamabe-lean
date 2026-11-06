import Yamabe3.Analysis.NativeFiniteCollarTrace
import Yamabe3.Analysis.NativeWeightedLift
import Yamabe3.Analysis.NativeAllScaleLocalH2
import Yamabe3.Analysis.WeightedTimeShiftEnergy

/-! One finite C2 angular field and its actual physical H2 jet at every
scale. No norm bound or global equation is inferred merely from C2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

def nativeFiniteAllScaleJet (m : Finset AngularIndex) (q : AngularIndex→ℝ→ℝ)
    (hq : ∀i∈m,ContDiff ℝ 2 (q i)) (s : ℝ) : nativeCollarJetClosure :=
  nativeFiniteCollarJet m (fun i => weightedTimeShift s (q i)) (fun i hi => weightedTimeShift_C2 s (hq i hi))

theorem finiteAngular_weightedTimeShift (m : Finset AngularIndex) (q : AngularIndex→ℝ→ℝ) (s : ℝ) :
    finiteAngular m (fun i => weightedTimeShift s (q i))=weightedCylinderShift s (finiteAngular m q) := by
  funext p
  simp only [finiteAngular,weightedTimeShift,weightedCylinderShift,Finset.mul_sum,mul_assoc]

theorem nativeFiniteAllScaleJet_same_field (m : Finset AngularIndex) (q : AngularIndex→ℝ→ℝ)
    (hq : ∀i∈m,ContDiff ℝ 2 (q i)) (s : ℝ) :
    ((nativeFiniteAllScaleJet m q hq s).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*finitePhysical m q (Real.exp (-s) • x)) := by
  have h := (nativeC2Collar_memLp (finitePhysical_contDiffOn_offZero_C2 m
    (fun i => weightedTimeShift s (q i)) (fun i hi => weightedTimeShift_C2 s (hq i hi)))).1.coeFn_toLp
  change ((nativeFiniteAllScaleJet m q hq s).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    finitePhysical m (fun i => weightedTimeShift s (q i)) at h
  filter_upwards [h] with x hx
  rw [hx,finitePhysical_eq_lift,finiteAngular_weightedTimeShift,cylinderLift_weightedCylinderShift,finitePhysical_eq_lift]

theorem nativeFiniteAllScaleJet_zero_eq (m : Finset AngularIndex) (q : AngularIndex→ℝ→ℝ)
    (hq : ∀i∈m,ContDiff ℝ 2 (q i)) :
    nativeFiniteAllScaleJet m q hq 0=nativeFiniteCollarJet m q hq := by
  apply nativeCollarJet_value_injective
  apply Lp.ext
  have h := nativeFiniteAllScaleJet_same_field m q hq 0
  have hz := (nativeC2Collar_memLp (finitePhysical_contDiffOn_offZero_C2 m q hq)).1.coeFn_toLp
  have h0 : ((nativeFiniteAllScaleJet m q hq 0).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] finitePhysical m q := by
    simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using h
  exact h0.trans hz.symm

theorem nativeFinitePhysical_localH2 (m : Finset AngularIndex) (q : AngularIndex→ℝ→ℝ)
    (hq : ∀i∈m,ContDiff ℝ 2 (q i)) :
    MemWkpLocally 2 (finitePhysical m q) ({0}ᶜ : Set E) := by
  apply native_all_scale_H2_local
  intro s
  exact (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2))
    (nativeFiniteAllScaleJet_same_field m q hq s)).mp (nativeCollarJetClosure_memH2 (nativeFiniteAllScaleJet m q hq s))

theorem nativeFiniteAngular_continuous (m : Finset AngularIndex) (q : AngularIndex→ℝ→ℝ)
    (hq : ∀i∈m,ContDiff ℝ 2 (q i)) : Continuous (finiteAngular m q) := by
  apply continuous_finsetSum
  intro i hi
  exact ((hq i hi).continuous.comp continuous_fst).mul ((smooth_angularRepresentative i).continuous.comp continuous_snd)

#print axioms finiteAngular_weightedTimeShift
#print axioms nativeFiniteAllScaleJet_same_field
#print axioms nativeFiniteAllScaleJet_zero_eq
#print axioms nativeFinitePhysical_localH2
#print axioms nativeFiniteAngular_continuous
end Yamabe3.Analysis.SpherePolar
