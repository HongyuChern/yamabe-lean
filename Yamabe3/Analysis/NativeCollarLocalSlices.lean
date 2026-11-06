import Yamabe3.Analysis.NativeCollarLiftRepresentative

/-! Physical equality on the collar requires angular slice equality only
on its actual time interval. No assertion about a negative-time PDE or a
volume representative restricted to a sphere is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar

theorem native_collar_lift_ae_eq_of_local_slices
    {w z : ℝ × S → ℝ} (hw : Measurable w) (hz : Measurable z)
    (hae : ∀ t∈Ioo (-(1/2:ℝ)) (1/2),(fun θ => w (t,θ))=ᵐ[angularVolume] (fun θ => z (t,θ))) :
    cylinderLift w=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift z := by
  let T : Set (ℝ × S) := Prod.fst ⁻¹' Ioo (-(1/2:ℝ)) (1/2)
  have hT : MeasurableSet T := measurableSet_Ioo.preimage measurable_fst
  have hlocal (v : ℝ × S → ℝ) (x : E) (hx : x∈nativePoissonEntranceCollar) :
      cylinderLift (T.indicator v) x=cylinderLift v x := by
    let y : puncturedSpace := ⟨x,hx.1⟩
    change cylinderLift _ (y:E)=cylinderLift _ (y:E)
    rw [cylinderLift_coe,cylinderLift_coe]
    unfold puncturedCylinderLift
    rw [Set.indicator_of_mem (show cylinderCoordinates y∈T from hx.2)]
  have hall : ∀ t,(fun θ => T.indicator w (t,θ))=ᵐ[angularVolume]
      (fun θ => T.indicator z (t,θ)) := by
    intro t
    by_cases ht : t∈Ioo (-(1/2:ℝ)) (1/2)
    · filter_upwards [hae t ht] with θ hθ
      rw [Set.indicator_of_mem (show (t,θ)∈T from ht),Set.indicator_of_mem (show (t,θ)∈T from ht)]
      exact hθ
    · exact Eventually.of_forall fun θ => by
        change T.indicator w (t,θ)=T.indicator z (t,θ)
        rw [Set.indicator_of_notMem (show (t,θ)∉T from ht),Set.indicator_of_notMem (show (t,θ)∉T from ht)]
  have h := native_collar_lift_ae_eq_of_joint_slices (hw.indicator hT) (hz.indicator hT) hall
  filter_upwards [h,ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hxm
  rw [hlocal w x hxm,hlocal z x hxm] at hx
  exact hx

#print axioms native_collar_lift_ae_eq_of_local_slices
end Yamabe3.Analysis.SpherePolar
