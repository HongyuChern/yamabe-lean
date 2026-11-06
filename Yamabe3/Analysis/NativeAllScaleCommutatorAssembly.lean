import Yamabe3.Analysis.NativeFiniteGlobalCommutatorAssembly
import Yamabe3.Analysis.NativeFiniteAnnularExtension

/-! The genuine all-scale SAME field determines the finite physical
cutoff source. A single compact local extension is constructed and then
eliminated by equality on every retained annulus. No global H1 or extra
regularity assumption is added to the original field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration

 theorem nativeAllScale_cutoff_commutator_assembly
    (J:ℝ→nativeCollarJetClosure) (u:E→ℝ)
    (hJ:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hs:∀x:E,x∉nativeSourceShell→∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    (S:ℝ) (N:ℕ) (hS:S≤-(1/4:ℝ)) (hN:-S+1/4≤(N:ℝ)/2):
    (fun x:E=>∑i:Fin N,nativePhysicalShellSource 1 (nativeOuterLogShellCenter i)
      (nativeCollarCutoffCommutatorCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
        (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J (nativeOuterLogShellCenter i)).val) x)=ᵐ[volume]
      physicalCutoffSource halfEndBasicAnnulus χ (weightedPhysicalDilation S u) S 1:=by
  let T:Option (Fin N)→ℝ:=fun i=>i.elim S (fun j=>nativeOuterLogShellCenter j)
  obtain ⟨v,hvc,hv,he⟩:=nativeLocalH2_finite_annular_extension (nativeAllScale_same_field_localH2 J hJ) T
  have hsub:nativePoissonEntranceCollar⊆halfEndBasicAnnulus:=
    subset_closure.trans nativeEntranceCollar_closure_subset_basic
  have hJv(i:Fin N):(J (nativeOuterLogShellCenter i)).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      weightedPhysicalDilation (nativeOuterLogShellCenter i) v:=by
    filter_upwards [hJ (nativeOuterLogShellCenter i),ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hxO
    exact hx.trans (he (some i) (hsub hxO)).symm
  have hsum:=nativeFiniteGlobal_cutoff_commutator_assembly (hv.le_of_le (by norm_num:1≤2)) χ hχ hs S N hS hN
    (fun i=>J (nativeOuterLogShellCenter i)) hJv
  have heS:weightedPhysicalDilation S v=ᵐ[volume.restrict halfEndBasicAnnulus]weightedPhysicalDilation S u:=by
    filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
    exact he none hx
  exact hsum.trans (physicalCutoffSource_congr_ae halfEndBasicAnnulus_isOpen χ heS S 1)

#print axioms nativeAllScale_cutoff_commutator_assembly
end Yamabe3.Analysis.SpherePolar
