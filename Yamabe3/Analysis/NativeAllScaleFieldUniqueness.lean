import Yamabe3.Analysis.NativeAllScaleLocalH2
import Yamabe3.Analysis.FiniteWeightedDilation
import Mathlib.Topology.Bases

/-! All actual weighted collar rows determine ONE physical volume class.
A countable open subcover is used explicitly, rather than an invalid
uncountable intersection of almost-everywhere equalities. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic

 theorem native_all_scale_field_unique {u v:E→ℝ}
    (h:∀s:ℝ,weightedPhysicalDilation s u=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s v):
    u=ᵐ[volume]v:=by
  have he(s:ℝ):u=ᵐ[volume.restrict (nativePhysicalScaleWindow s)]v:=by
    have hd:=ae_comp_dilation (Real.exp_ne_zero s) (h s)
    filter_upwards [hd] with x hx
    change Real.exp (3*s/2)*u (Real.exp (-s) • (Real.exp s • x))=
      Real.exp (3*s/2)*v (Real.exp (-s) • (Real.exp s • x)) at hx
    simp only [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul] at hx
    exact mul_left_cancel₀ (Real.exp_ne_zero (3*s/2)) hx
  have hUnion:(⋃s:ℝ,nativePhysicalScaleWindow s)=({0}ᶜ:Set E):=by
    ext x
    constructor
    · intro hx
      obtain ⟨s,hs⟩:=mem_iUnion.mp hx
      exact nativePhysicalScaleWindow_off_zero s hs
    · intro hx
      exact mem_iUnion.mpr ⟨-Real.log ‖x‖,nativePhysicalScaleWindow_covers hx⟩
  obtain ⟨T,hT,hcover⟩:=TopologicalSpace.isOpen_iUnion_countable nativePhysicalScaleWindow nativePhysicalScaleWindow_open
  have hfull:u=ᵐ[volume.restrict (⋃s∈T,nativePhysicalScaleWindow s)]v:=
    (ae_eq_restrict_biUnion_iff nativePhysicalScaleWindow hT u v).mpr (fun s _=>he s)
  rw [hcover,hUnion] at hfull
  have hh:=(ae_restrict_iff' isClosed_singleton.isOpen_compl.measurableSet).mp hfull
  filter_upwards [hh,volume.ae_ne (0:E)] with x hx hx0
  exact hx hx0

 theorem native_all_scale_jet_same_volume_class (J:ℝ→nativeCollarJetClosure) {u v:E→ℝ}
    (hu:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u)
    (hv:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s v):
    u=ᵐ[volume]v:=native_all_scale_field_unique (fun s=>(hu s).symm.trans (hv s))

#print axioms native_all_scale_field_unique
#print axioms native_all_scale_jet_same_volume_class
end Yamabe3.Analysis.SpherePolar
