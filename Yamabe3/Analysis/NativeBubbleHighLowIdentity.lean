import Yamabe3.Analysis.NativeExteriorModelJacobian

/-! The same exterior H2 jet has the actual low-plus-high physical
representative. Only the high infinite series requires a measurable
representative, which is constructed here and not added as an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem exists_nativeBubbleHighLow_same_physical_field (t₀ : ℝ)
    (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)) (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    let B := fullBubbleHighPotential (-t₀)
    let K := nativeBubbleLowCollarJet t₀ q hq+nativePoissonExteriorCollarJet B b hb
    ∃w : ℝ × S → ℝ,StronglyMeasurable w ∧
      (∀t,t≤0 → (fun θ => w (t,θ))=ᵐ[angularVolume] (B.curve b (-t) : S → ℝ)) ∧
      (K.val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun x => finitePhysical nativeLowIndexFinset (fun i t => q i (t₀+t)) x+cylinderLift w x) := by
  dsimp only
  obtain ⟨w,hw,hwneg,he,-,-,-⟩ := exists_nativePoissonExterior_same_curve_H2_collar
    (fullBubbleHighPotential (-t₀)) b hb
  refine ⟨w,hw,hwneg,?_⟩
  let L := nativeBubbleLowCollarJet t₀ q hq
  let H := nativePoissonExteriorCollarJet (fullBubbleHighPotential (-t₀)) b hb
  have hl : (L.val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      finitePhysical nativeLowIndexFinset (fun i t => q i (t₀+t)) :=
    (nativeC2Collar_memLp (finitePhysical_contDiffOn_offZero_C2 _ _
      (fun i hi => (hq i hi).comp (contDiff_const.add contDiff_id)))).1.coeFn_toLp
  change (H.val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w at he
  change ((L+H).val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] _
  filter_upwards [Lp.coeFn_add L.val.1 H.val.1,hl,he] with x ha hl hh
  change (L.val.1+H.val.1) x=_
  rw [ha]
  simp only [Pi.add_apply,hl,hh]

#print axioms exists_nativeBubbleHighLow_same_physical_field
end Yamabe3.Analysis.SpherePolar
