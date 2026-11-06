import Yamabe3.Analysis.NativeAllScaleCommutatorFiniteSingle
import Yamabe3.Analysis.NativePhysicalShellPairing

/-! The SAME complete finite commutator source has exactly the fixed-S
full spectral pairing. Its true physical integrals are used to establish
this identity, preserving all angular modes and the factor8. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration

 theorem nativeAllScale_cutoff_commutator_spectral_assembly
    (J:ℝ→nativeCollarJetClosure) (u:E→ℝ)
    (hJ:∀s:ℝ,(J s).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]weightedPhysicalDilation s u)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hs:∀x:E,x∉nativeSourceShell→∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    (S:ℝ) (N:ℕ) (hS:S≤-(1/4:ℝ)) (hN:-S+1/4≤(N:ℝ)/2)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ):
    (∑i:Fin N,inner ℝ (nativeFullShellSourceReturnCLM (nativeOuterLogShellCenter i)
      (nativeCollarCutoffCommutatorCLM (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
        (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J (nativeOuterLogShellCenter i)).val))
        (nativePhysicalPairTestL2 φ hφ hc h0))=
      inner ℝ (nativeFullShellSourceReturnCLM S (nativeCollarCutoffCommutatorCLM χ hχ (J S).val))
        (nativePhysicalPairTestL2 φ hφ hc h0):=by
  let U:Fin N→NativeCollarL2:=fun i=>nativeCollarCutoffCommutatorCLM
    (nativeOuterFieldCutoffAtScale S (nativeOuterLogShellCenter i) χ)
    (nativeOuterFieldCutoffAtScale_smooth S (nativeOuterLogShellCenter i) hχ) (J (nativeOuterLogShellCenter i)).val
  have he:=nativeAllScale_cutoff_commutator_finite_eq_single J u hJ χ hχ hs 1 S N hS hN
  have hφm:MemLp φ 2 (volume:Measure E):=hφ.continuous.memLp_of_hasCompactSupport hc
  have hp(s:ℝ)(U:NativeCollarL2):
      (∫x:E,nativePhysicalShellSource 1 s U x*φ x)=
        8*inner ℝ (nativeFullShellSourceReturnCLM s U) (nativePhysicalPairTestL2 φ hφ hc h0):=by
    simpa only [inv_one,one_smul,mul_one] using
      nativePhysicalShellSource_full_pairing (by norm_num:(0:ℝ)<1) s U φ hφ hc h0
  have hh:(∑i:Fin N,∫x:E,nativePhysicalShellSource 1 (nativeOuterLogShellCenter i) (U i) x*φ x)=
      ∫x:E,nativePhysicalShellSource 1 S (nativeCollarCutoffCommutatorCLM χ hχ (J S).val) x*φ x:=by
    calc
      _=(∫x:E,(∑i:Fin N,nativePhysicalShellSource 1 (nativeOuterLogShellCenter i) (U i) x)*φ x):=by
        simpa only [Pi.mul_apply,Finset.sum_mul] using
          (integral_finsetSum Finset.univ (fun (i:Fin N) _=>(nativePhysicalShellSource_memLp_two 1 (nativeOuterLogShellCenter i) (U i)).integrable_mul hφm)).symm
      _=_:=by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        exact congrArg (fun r:ℝ=>r*φ x) hx
  simp_rw [hp] at hh
  rw [←Finset.mul_sum] at hh
  exact (mul_left_cancel₀ (by norm_num:(8:ℝ)≠0) hh)

#print axioms nativeAllScale_cutoff_commutator_spectral_assembly
end Yamabe3.Analysis.SpherePolar
