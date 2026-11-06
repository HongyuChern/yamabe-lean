import Yamabe3.Analysis.NativeFiniteAllScaleField
import Yamabe3.Analysis.NativeCollarLiftRepresentative

/-! Exact addition and subtraction for already proved representatives of
actual collar jets. These lemmas transport identities, not existence. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar

abbrev NativeScaledJetRep (J : nativeCollarJetClosure) (s : ℝ) (w : ℝ×S→ℝ) : Prop :=
  (J.val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
    (fun x => Real.exp (3*s/2)*cylinderLift w (Real.exp (-s) • x))

theorem native_cylinderLift_sub (w z : ℝ×S→ℝ) :
    cylinderLift (fun p => w p-z p)=fun x => cylinderLift w x-cylinderLift z x := by
  have h := native_cylinderLift_add w (fun p => (-1:ℝ)*z p)
  rw [native_cylinderLift_smul] at h
  simpa only [neg_one_mul,sub_eq_add_neg] using h

theorem NativeScaledJetRep.add {J K : nativeCollarJetClosure} {s : ℝ} {w z : ℝ×S→ℝ}
    (hJ : NativeScaledJetRep J s w) (hK : NativeScaledJetRep K s z) :
    NativeScaledJetRep (J+K) s (fun p => w p+z p) := by
  filter_upwards [hJ,hK,Lp.coeFn_add J.val.1 K.val.1] with x hj hk ha
  change (J.val.1+K.val.1 : NativeCollarL2) x=_
  rw [ha]
  change J.val.1 x+K.val.1 x=_
  rw [hj,hk,native_cylinderLift_add]
  ring

theorem NativeScaledJetRep.sub {J K : nativeCollarJetClosure} {s : ℝ} {w z : ℝ×S→ℝ}
    (hJ : NativeScaledJetRep J s w) (hK : NativeScaledJetRep K s z) :
    NativeScaledJetRep (J-K) s (fun p => w p-z p) := by
  filter_upwards [hJ,hK,Lp.coeFn_sub J.val.1 K.val.1] with x hj hk ha
  change (J.val.1-K.val.1 : NativeCollarL2) x=_
  rw [ha]
  change J.val.1 x-K.val.1 x=_
  rw [hj,hk,native_cylinderLift_sub]
  ring

#print axioms native_cylinderLift_sub
#print axioms NativeScaledJetRep.add
#print axioms NativeScaledJetRep.sub
end Yamabe3.Analysis.SpherePolar
