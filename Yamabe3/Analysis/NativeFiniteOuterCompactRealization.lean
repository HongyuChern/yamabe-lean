import Yamabe3.Analysis.NativeFiniteAnnularExtension
import Yamabe3.Analysis.NativeOuterCutoffActualOperator
import Yamabe3.Analysis.BoundaryLocalizedMultiplier
import Yamabe3.Analysis.PhysicalOuterWindowGeometry

/-! One compact global H2 auxiliary field realizes the SAME cutoff
outer field on the complete finite physical window and all its retained
closed jets. It is fixed before all tests; it does not assert an exterior
PDE or replace the original global completed field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization

 theorem exists_nativeFinite_outer_compact_H2_realization
    (J:ℝ→nativeCollarJetClosure) (u:E→ℝ)
    (hJ:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (S:ℝ) (N:ℕ):
    ∃v:E→ℝ,HasCompactSupport v ∧ MemWkp 2 2 v univ ∧
      EqOn v (fun x=>χ (Real.exp S • x)*u x) (nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0)) ∧
      (∀x:E,χ (Real.exp S • x)=0→v x=0) ∧
      ∀i:Fin N,
        ((nativeCollarCutoffCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
          (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J (nativeOuterLogShellCenter i))).val.1:E→ℝ)
          =ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation (nativeOuterLogShellCenter i) v:=by
  obtain ⟨v₀,hv₀c,hv₀,he⟩:=nativeLocalH2_finite_annular_extension (nativeAllScale_same_field_localH2 J hJ)
    (fun i:Fin N=>nativeOuterLogShellCenter i)
  let χp:E→ℝ:=fun x=>χ (Real.exp S • x)
  have hχp:ContDiff ℝ ∞ χp:=hχ.comp (contDiff_id.const_smul _)
  have hcχp:HasCompactSupport χp:=hc.comp_homeomorph (Homeomorph.smulOfNeZero (Real.exp S) (Real.exp_ne_zero S))
  let v:E→ℝ:=fun x=>χp x*v₀ x
  have hv:MemWkp 2 2 v univ:=memWkp_mul_smooth_of_tsupport_subset 2 isOpen_univ isOpen_univ
    (by simpa only [inter_univ] using hv₀) hχp hcχp (subset_univ _)
  have he₀:EqOn v₀ u (nativePolarTimeWindow (Ioc (-(N:ℝ)/2) 0)):=by
    intro x hx
    have hxU:x∈⋃i:Fin N,nativeScaledSourceShell (nativeOuterLogShellCenter i):=by
      rw [nativeScaledOuterWindow_union]
      exact hx
    obtain ⟨i,hi⟩:=mem_iUnion.mp hxU
    have hys:Real.exp (nativeOuterLogShellCenter i) • x∈halfEndBasicAnnulus:=
      nativeSourceShell_subset_collar.trans (subset_closure.trans nativeEntranceCollar_closure_subset_basic) hi
    have heq:=he i hys
    change Real.exp (3*nativeOuterLogShellCenter i/2)*v₀ (Real.exp (-nativeOuterLogShellCenter i) • (Real.exp (nativeOuterLogShellCenter i) • x))=
      Real.exp (3*nativeOuterLogShellCenter i/2)*u (Real.exp (-nativeOuterLogShellCenter i) • (Real.exp (nativeOuterLogShellCenter i) • x)) at heq
    simp only [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul] at heq
    exact mul_left_cancel₀ (Real.exp_ne_zero _) heq
  refine ⟨v,hcχp.mul_right,hv,fun x hx=>?_,fun x hx=>?_,fun i=>?_⟩
  · exact congrArg (fun r:ℝ=>χp x*r) (he₀ hx)
  · change χp x*v₀ x=0
    change χp x=0 at hx
    rw [hx,zero_mul]
  · have hJv:(J (nativeOuterLogShellCenter i)).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
        weightedPhysicalDilation (nativeOuterLogShellCenter i) v₀:=by
      filter_upwards [hJ (nativeOuterLogShellCenter i),ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with y hy hyO
      exact hy.trans (he i (subset_closure.trans nativeEntranceCollar_closure_subset_basic hyO)).symm
    have hh:=nativeOuterCutoff_same_physical_field S (nativeOuterLogShellCenter i) χ hχ (J (nativeOuterLogShellCenter i)) hJv
    exact hh

#print axioms exists_nativeFinite_outer_compact_H2_realization
end Yamabe3.Analysis.SpherePolar
