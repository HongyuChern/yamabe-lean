import Yamabe3.Analysis.L2ZeroExtension
import Yamabe3.Analysis.EuclideanCompletedDilation
import Yamabe3.Analysis.NativeOuterWindowSourceSupport
import Yamabe3.Analysis.L2MeasureRestriction

/-! An actual restricted physical L2 source gives a bounded source in
one fixed exterior time window. Its radial weight is exp(-s/2), with the
same physical representative under the true Euclidean dilation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay

private theorem l2Endomorphism_cast_ae {μ ν:Measure E} (h:μ=ν)
    (T:Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f:(E→ℝ)→E→ℝ)
    (hT:∀U:Lp ℝ 2 μ,(T U:E→ℝ)=ᵐ[μ]f U) :
    ∀U:Lp ℝ 2 ν,((h ▸ T) U:E→ℝ)=ᵐ[ν]f U := by
  subst ν
  exact hT

def volumeL2DilationCLM (s:ℝ) (hs:s ≤ 0) : Lp ℝ 2 (volume:Measure E) →L[ℝ] Lp ℝ 2 (volume:Measure E) :=
  (native_euclideanMetric_volumeMeasure 3) ▸
    euclideanL2DilationCLM (Real.exp_pos s) (Real.exp_le_one_iff.mpr hs)

theorem volumeL2DilationCLM_ae (s:ℝ) (hs:s ≤ 0) (U:Lp ℝ 2 (volume:Measure E)) :
    (volumeL2DilationCLM s hs U:E→ℝ)=ᵐ[volume]fun x=>U (Real.exp (-s) • x) := by
  apply l2Endomorphism_cast_ae (h:=native_euclideanMetric_volumeMeasure 3)
    (T:=euclideanL2DilationCLM (Real.exp_pos s) (Real.exp_le_one_iff.mpr hs))
    (f:=fun f x=>f (Real.exp (-s) • x)) (hT:=?_) U
  intro f
  have hh:=euclideanL2DilationCLM_ae (Real.exp_pos s) (Real.exp_le_one_iff.mpr hs) f
  simpa only [←Real.exp_neg] using hh

def physicalL2ScaledCollarCLM (O:Set E) (hO:MeasurableSet O) (s:ℝ) (hs:s ≤ 0) :
    Lp ℝ 2 (volume.restrict O) →L[ℝ] NativeCollarL2 :=
  (Real.exp (-s/2):ℝ) • ((l2MeasureRestrictCLM (ν:=volume.restrict nativePoissonEntranceCollar)
    Measure.restrict_le_self).comp ((volumeL2DilationCLM s hs).comp (l2ZeroExtendCLM O hO)))

theorem physicalL2ScaledCollarCLM_ae (O:Set E) (hO:MeasurableSet O) (s:ℝ) (hs:s ≤ 0)
    (U:Lp ℝ 2 (volume.restrict O)) :
    (physicalL2ScaledCollarCLM O hO s hs U:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (-s/2)*O.indicator (U:E→ℝ) (Real.exp (-s) • y) := by
  let Z:=l2ZeroExtendCLM O hO U
  let D:=volumeL2DilationCLM s hs Z
  let T:=l2MeasureRestrictCLM (ν:=volume.restrict nativePoissonEntranceCollar) Measure.restrict_le_self D
  have hz:∀ᵐy:E∂volume,Z (Real.exp (-s) • y)=O.indicator (U:E→ℝ) (Real.exp (-s) • y) := by
    change (fun y:E=>l2ZeroExtend O hO U (Real.exp (-s) • y))=ᵐ[volume]_
    simpa only [preimage_univ,Measure.restrict_univ] using
      ae_comp_dilation (Real.exp_ne_zero (-s)) (ae_restrict_of_ae (s:=univ) (l2ZeroExtend_ae O hO U))
  filter_upwards [Lp.coeFn_smul (Real.exp (-s/2)) T,
    l2MeasureRestrict_ae (ν:=volume.restrict nativePoissonEntranceCollar) Measure.restrict_le_self D,
    ae_restrict_of_ae (s:=nativePoissonEntranceCollar) (volumeL2DilationCLM_ae s hs Z),
    ae_restrict_of_ae (s:=nativePoissonEntranceCollar) hz] with y hm ht hd hz
  change (Real.exp (-s/2) • T:NativeCollarL2) y=_
  rw [hm]
  change Real.exp (-s/2)*T y=_
  change T y=D y at ht
  change D y=Z (Real.exp (-s) • y) at hd
  rw [ht,hd,hz]

def physicalL2OuterWindowSourceCLM (O:Set E) (hO:MeasurableSet O) (m:ℕ) :
    Lp ℝ 2 (volume.restrict O) →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ) :=
  nativeFiniteOuterWindowSourceCLM m (fun i=>physicalL2ScaledCollarCLM O hO
    (nativeOuterLogShellCenter i) (by dsimp only [nativeOuterLogShellCenter];have hi:0 ≤ (i.val:ℝ):=Nat.cast_nonneg _;linarith))

theorem physicalL2OuterWindowSource_lower_support (O:Set E) (hO:MeasurableSet O) (m:ℕ)
    (U:Lp ℝ 2 (volume.restrict O)) :
    ∀ᵐt:ℝ∂volume,t < -(m:ℝ)/2-1 → physicalL2OuterWindowSourceCLM O hO m U t=0 :=
  nativeFiniteOuterWindowSource_lower_support m _ U

#print axioms volumeL2DilationCLM_ae
#print axioms physicalL2ScaledCollarCLM_ae
#print axioms physicalL2OuterWindowSource_lower_support
end Yamabe3.Analysis.SpherePolar
