import Yamabe3.Analysis.NativeLocalH2ScaledSource
import Yamabe3.Analysis.NativeAllScaleLocalH2

/-! One auxiliary compact Sobolev extension agrees with the SAME
original field on every member of a retained finite annular family.
This is used only to compare local weak commutators; it does not replace
the solution field, its source, or its boundary values. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic

 theorem nativeLocalH2_finite_annular_extension
    {ι:Type*} [Finite ι] {u:E→ℝ} (hu:MemWkpLocally 2 u ({0}ᶜ:Set E)) (T:ι→ℝ):
    ∃v:E→ℝ,HasCompactSupport v ∧ MemWkp 2 2 v univ ∧
      ∀i:ι,EqOn (weightedPhysicalDilation (T i) v) (weightedPhysicalDilation (T i) u) halfEndBasicAnnulus:=by
  let K:ι→Set E:=fun i=>(fun x:E=>Real.exp (-T i) • x) '' closure halfEndBasicAnnulus
  have hK(i:ι):IsCompact (K i):=
    nativeBasicAnnulus_precompact_off_zero.1.image (continuous_const_smul _)
  have hK0:(⋃i:ι,K i)⊆({0}ᶜ:Set E):=by
    rintro y hy
    obtain ⟨i,x,hx,rfl⟩:=by simpa only [K,mem_iUnion,mem_image] using hy
    intro hz
    exact nativeBasicAnnulus_precompact_off_zero.2 hx
      ((smul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero (-T i)))
  obtain ⟨v,U,hU,hKU,hvc,hv,he⟩:=exists_compact_sobolev_extension_near_compact hu (isCompact_iUnion hK) hK0
  refine ⟨v,hvc,hv,fun i x hx=>?_⟩
  have hxU:Real.exp (-T i) • x∈U:=hKU (mem_iUnion.mpr ⟨i,x,subset_closure hx,rfl⟩)
  exact congrArg (fun q:ℝ=>Real.exp (3*T i/2)*q) (he hxU)

 theorem nativeAllScale_same_field_localH2
    (J:ℝ→nativeCollarJetClosure) {u:E→ℝ}
    (hJ:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u):
    MemWkpLocally 2 u ({0}ᶜ:Set E):=by
  apply native_all_scale_H2_local
  intro s
  exact (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) (hJ s)).mp
    (nativeCollarJetClosure_memH2 (J s))

#print axioms nativeLocalH2_finite_annular_extension
#print axioms nativeAllScale_same_field_localH2
end Yamabe3.Analysis.SpherePolar
