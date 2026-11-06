import Yamabe3.Analysis.NativeFullCollarSourceSupport
import Yamabe3.Analysis.NativeSupportedReverseSource

/-! Locality of the actual low L2 physical lift, and exact collar
reconstruction for any supported source cutoff. The cutoff can move
past the collar because the source itself vanishes where it differs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeL2LowPhysicalSource_zero_of_time_zero
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t∈Icc (-(1/2:ℝ)) (1/2) → F t=0) :
    nativeL2LowPhysicalSourceCLM F=0 := by
  apply nativeL2CollarLift_zero_of_time_zero
  filter_upwards [nativeL2LowAngularCLM_ae F,hF] with t ht hf
  intro h
  change nativeL2LowAngularCLM F t=0
  rw [ht,hf h,map_zero,map_zero]

theorem nativeL2LowPhysicalSource_locality
    (F G : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hFG : ∀ᵐt : ℝ ∂volume,t∈Icc (-(1/2:ℝ)) (1/2) → F t=G t) :
    nativeL2LowPhysicalSourceCLM F=nativeL2LowPhysicalSourceCLM G := by
  apply sub_eq_zero.mp
  rw [←map_sub]
  apply nativeL2LowPhysicalSource_zero_of_time_zero
  filter_upwards [Lp.coeFn_sub F G,hFG] with t ht hf
  intro h
  rw [ht]
  change F t-G t=0
  rw [hf h,sub_self]

theorem nativeSupportedReverseSource_local_reconstruction (b : ℝ)
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hF : ∀ᵐt : ℝ ∂volume,t<b → F t=0) :
    nativeLowReverseL2SourceCLM (nativeSupportedReverseSourcePrepareCLM b F)=nativeL2LowPhysicalSourceCLM F := by
  have he : nativeL2LowPhysicalSourceCLM (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F)=
      nativeL2LowPhysicalSourceCLM (spectralL2PotentialMulCLM nativeReverseSourceWeight F) := by
    apply nativeL2LowPhysicalSource_locality
    filter_upwards [spectralL2PotentialMul_coe_ae (nativeSupportedReverseWeight b) F,
      spectralL2PotentialMul_coe_ae nativeReverseSourceWeight F,hF] with t hb ho hf
    intro ht
    change spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F t=nativeSupportedReverseWeight b t • F t at hb
    change spectralL2PotentialMulCLM nativeReverseSourceWeight F t=nativeReverseSourceWeight t • F t at ho
    rw [hb,ho]
    by_cases htb : b≤t
    · rw [nativeSupportedReverseWeight_eq b t htb,nativeReverseSourceWeight_eq t
        (show t∈Icc (-1:ℝ) 1 by constructor <;> linarith [ht.1,ht.2])]
    · rw [hf (lt_of_not_ge htb),smul_zero,smul_zero]
  change nativeInverseFourthPowerCollarCLM
    (nativeL2LowPhysicalSourceCLM (l2TimeReflectCLM AngularSpectralSpace
      (l2TimeReflectCLM AngularSpectralSpace (spectralL2PotentialMulCLM (nativeSupportedReverseWeight b) F))))=_
  rw [l2TimeReflect_involution,he]
  have ho := nativeLowReverseSourcePrepare_reconstructs F
  change nativeInverseFourthPowerCollarCLM
    (nativeL2LowPhysicalSourceCLM (l2TimeReflectCLM AngularSpectralSpace
      (l2TimeReflectCLM AngularSpectralSpace (spectralL2PotentialMulCLM nativeReverseSourceWeight F))))=_ at ho
  rw [l2TimeReflect_involution] at ho
  exact ho

#print axioms nativeL2LowPhysicalSource_zero_of_time_zero
#print axioms nativeL2LowPhysicalSource_locality
#print axioms nativeSupportedReverseSource_local_reconstruction
end Yamabe3.Analysis.SpherePolar
