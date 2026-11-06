import Yamabe3.Analysis.NativePhysicalCommutatorAssemblyScaling

/-! Finite shell commutators equal the SINGLE fixed-scale closed-jet
commutator of the same all-scale field. The auxiliary representative is
eliminated entirely from the resulting source identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration

 theorem nativeAllScale_cutoff_commutator_finite_eq_single
    (J:ℝ→nativeCollarJetClosure) (u:E→ℝ)
    (hJ:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hs:∀x:E,x∉nativeSourceShell→∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    (a S:ℝ) (N:ℕ) (hS:S≤-(1/4:ℝ)) (hN:-S+1/4≤(N:ℝ)/2):
    (fun x:E=>∑i:Fin N,nativePhysicalShellSource a (nativeOuterLogShellCenter i)
      (nativeCollarCutoffCommutatorCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
        (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J (nativeOuterLogShellCenter i)).val) x)=ᵐ[volume]
      nativePhysicalShellSource a S (nativeCollarCutoffCommutatorCLM χ hχ (J S).val):=by
  have hu:=nativeAllScale_same_field_localH2 J hJ
  have hunit:=nativeLocalH2_weighted_basicAnnulus hu S
  have hsum:=nativeAllScale_physical_cutoff_commutator_assembly J u hJ χ hχ hs a S N hS hN
  exact hsum.trans (nativeCollarCutoffCommutator_physical_identity χ hχ hs (J S)
    (hunit.le_of_le (by norm_num:1≤2)) (hJ S) a S).symm

#print axioms nativeAllScale_cutoff_commutator_finite_eq_single
end Yamabe3.Analysis.SpherePolar
