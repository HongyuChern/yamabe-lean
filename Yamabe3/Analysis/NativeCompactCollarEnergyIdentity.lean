import Yamabe3.Analysis.NativeCompactCollarEnergy
import Yamabe3.Analysis.L2EqualMeasureTransport

/-! The bounded energy lift of the closed jet retains its SAME actual
volume L2 value. Density extension is checked by equality of continuous
L2 operators; no point evaluation on arbitrary L2 data is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD
local notation "O" => nativePoissonEntranceCollar
variable (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆O)

def nativeCompactCollarValueCLM : nativeCollarJetClosure →L[ℝ] Lp ℝ 2 (volume:Measure E) :=
  (l2ZeroExtendCLM O (nativePolarTimeWindow_open (1/2)).measurableSet).comp
    ((nativeCollarScalarMulCLM χ hχ.continuous).comp
      (nativeCollarJetValueCLM.comp nativeCollarJetClosure.subtypeL))

theorem nativeCompactCollarValueCLM_ae (J:nativeCollarJetClosure) :
    (nativeCompactCollarValueCLM χ hχ J:E→ℝ)=ᵐ[volume]
      nativePoissonEntranceCollar.indicator (fun x=>χ x*(J.val.1:E→ℝ) x) := by
  have hmul:=nativeCollarScalarMulCLM_ae χ hχ.continuous J.val.1
  have hi: nativePoissonEntranceCollar.indicator
      (nativeCollarScalarMulCLM χ hχ.continuous J.val.1:E→ℝ)=ᵐ[volume]
        nativePoissonEntranceCollar.indicator (fun x=>χ x*(J.val.1:E→ℝ) x) :=
    (ae_eq_restrict_iff_indicator_ae_eq (nativePolarTimeWindow_open (1/2)).measurableSet).mp hmul
  exact (l2ZeroExtend_ae O (nativePolarTimeWindow_open (1/2)).measurableSet _).trans hi

theorem nativeCompactCollarEnergyCLM_toL2_operator :
    (l2EqualMeasureCLM (native_euclideanMetric_volumeMeasure 3)).comp
      ((toL2 D O).comp (nativeCompactCollarEnergyCLM χ hχ hc hs))=
        nativeCompactCollarValueCLM χ hχ := by
  let A:=(l2EqualMeasureCLM (native_euclideanMetric_volumeMeasure 3)).comp
    ((toL2 D O).comp (nativeCompactCollarEnergyCLM χ hχ hc hs))
  let B:=nativeCompactCollarValueCLM χ hχ
  apply ContinuousLinearMap.ext
  intro J
  have hclosed:=isClosed_eq A.continuous B.continuous
  refine nativeC2CollarJetInclusion_dense.induction_on J hclosed ?_
  intro u
  change l2EqualMeasureCLM (native_euclideanMetric_volumeMeasure 3)
    (toL2 D O (nativeCompactCollarEnergyCLM χ hχ hc hs (nativeC2CollarJetInclusion u)))=
      nativeCompactCollarValueCLM χ hχ (nativeC2CollarJetInclusion u)
  rw [nativeCompactCollarEnergyCLM_C2]
  apply Lp.ext
  have hraw:(nativeC2CollarValue u.property:E→ℝ)=ᵐ[volume.restrict O]u.val :=
    (nativeC2Collar_memLp u.property).1.coeFn_toLp
  have hind:nativePoissonEntranceCollar.indicator (fun x=>χ x*(nativeC2CollarValue u.property:E→ℝ) x)=ᵐ[volume]
      nativePoissonEntranceCollar.indicator (fun x=>χ x*u.val x) :=
    (ae_eq_restrict_iff_indicator_ae_eq (nativePolarTimeWindow_open (1/2)).measurableSet).mp
      ((EventuallyEq.refl _ _).mul hraw)
  filter_upwards [l2EqualMeasureCLM_ae (native_euclideanMetric_volumeMeasure 3)
      (toL2 D O (nativeC2CutoffEnergyElement χ hχ hc hs u)),
    nativeC2CutoffEnergyElement_ae χ hχ hc hs u,
    nativeCompactCollarValueCLM_ae χ hχ (nativeC2CollarJetInclusion u),hind] with x hcast hE hB hi
  rw [hcast,hE,hB]
  change χ x*u.val x=nativePoissonEntranceCollar.indicator (fun x=>χ x*(nativeC2CollarValue u.property:E→ℝ) x) x
  rw [hi]
  by_cases hx:x∈O
  · exact (indicator_of_mem hx (fun y:E=>χ y*u.val y)).symm
  · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h=>hx (hs h)),zero_mul]

theorem nativeCompactCollarEnergyCLM_ae (J:nativeCollarJetClosure) :
    (toL2 D O (nativeCompactCollarEnergyCLM χ hχ hc hs J):E→ℝ)=ᵐ[volume]
      nativePoissonEntranceCollar.indicator (fun x=>χ x*(J.val.1:E→ℝ) x) := by
  have he:=congrArg (fun T:nativeCollarJetClosure →L[ℝ] Lp ℝ 2 (volume:Measure E)=>T J)
    (nativeCompactCollarEnergyCLM_toL2_operator χ hχ hc hs)
  have hcast:=l2EqualMeasureCLM_ae (native_euclideanMetric_volumeMeasure 3)
    (toL2 D O (nativeCompactCollarEnergyCLM χ hχ hc hs J))
  change l2EqualMeasureCLM (native_euclideanMetric_volumeMeasure 3)
    (toL2 D O (nativeCompactCollarEnergyCLM χ hχ hc hs J))=nativeCompactCollarValueCLM χ hχ J at he
  rw [he] at hcast
  exact hcast.symm.trans (nativeCompactCollarValueCLM_ae χ hχ J)

#print axioms nativeCompactCollarValueCLM_ae
#print axioms nativeCompactCollarEnergyCLM_toL2_operator
#print axioms nativeCompactCollarEnergyCLM_ae
end Yamabe3.Analysis.SpherePolar
