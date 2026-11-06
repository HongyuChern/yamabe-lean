import Yamabe3.Analysis.NativeShellCutoff
import Yamabe3.Analysis.NativePhysicalShellCriticalTransport
import Yamabe3.Analysis.WeakCutoffCriticalGlobal
import Yamabe3.Analysis.WeakLaplacianDilation

/-! The shell source really IS the complete physical cutoff residual
when the actual cutoff derivatives vanish off the shell. This proves the
operator identity missing from a norm-only partial-source construction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Sobolev.Euclidean

 theorem weakCutoffCommutator_zero_of_derivative_support
    (O:Set E) (χ u:E→ℝ)
    (hχ:∀x:E,x∉nativeSourceShell → ∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    {x:E} (hx:x∉nativeSourceShell) : weakCutoffCommutator O χ u x=0 := by
  simp only [weakCutoffCommutator,(hχ x hx _).1,(hχ x hx _).2,zero_mul,mul_zero,add_zero,
    Finset.sum_const_zero,neg_zero]

theorem nativePhysicalShellSource_eq_physicalCutoff
    {O:Set E} (hO:MeasurableSet O) (hSO:nativeSourceShell⊆O) (χ u:E→ℝ)
    (hχ:∀x:E,x∉nativeSourceShell → ∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    (U:NativeCollarL2)
    (hU:(U:E→ℝ)=ᵐ[volume.restrict nativeSourceShell]weakCutoffCommutator O χ u)
    (a s:ℝ) : nativePhysicalShellSource a s U=ᵐ[volume]physicalCutoffSource O χ u s a := by
  have hb:nativeZeroShellSource U=ᵐ[volume]O.indicator (weakCutoffCommutator O χ u) := by
    filter_upwards [(ae_restrict_iff' nativeSourceShell_measurable).mp hU] with x hx
    by_cases hs:x∈nativeSourceShell
    · simp only [nativeZeroShellSource,indicator_of_mem hs,indicator_of_mem (hSO hs),hx hs]
    · rw [nativeZeroShellSource,indicator_of_notMem hs]
      by_cases ho:x∈O
      · rw [indicator_of_mem ho,weakCutoffCommutator_zero_of_derivative_support O χ u hχ hs]
      · rw [indicator_of_notMem ho]
  have hd:=ae_comp_dilation (Real.exp_ne_zero (s-Real.log a)) (ae_restrict_of_ae (s:=univ) hb)
  simp only [preimage_univ,Measure.restrict_univ] at hd
  filter_upwards [hd] with x hx
  change 8*Real.exp (-2*Real.log a+s/2)*nativeZeroShellSource U (Real.exp (s-Real.log a) • x)=_
  rw [hx]
  unfold physicalCutoffSource physicalCutoffAnnulus
  by_cases ho:Real.exp (s-Real.log a) • x∈O
  · rw [indicator_of_mem ho,indicator_of_mem (show x∈(fun y:E=>Real.exp (s-Real.log a) • y) ⁻¹' O from ho)]
  · rw [indicator_of_notMem ho,indicator_of_notMem (show x∉(fun y:E=>Real.exp (s-Real.log a) • y) ⁻¹' O from ho),mul_zero]

theorem nativeCollarCutoffCommutator_physical_identity
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ)
    (hs:∀x:E,x∉nativeSourceShell → ∀i:Fin 3,
      partialDeriv i χ x=0 ∧ partialDeriv i (partialDeriv i χ) x=0)
    (J:nativeCollarJetClosure) {u:E→ℝ} (hu:MemWkp 1 2 u halfEndBasicAnnulus)
    (hv:(J.val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]u) (a s:ℝ) :
    nativePhysicalShellSource a s (nativeCollarCutoffCommutatorCLM χ hχ J.val)=ᵐ[volume]
      physicalCutoffSource halfEndBasicAnnulus χ u s a := by
  apply nativePhysicalShellSource_eq_physicalCutoff halfEndBasicAnnulus_isOpen.measurableSet
    (nativeSourceShell_subset_collar.trans (subset_closure.trans nativeEntranceCollar_closure_subset_basic)) χ u hs
  exact ae_mono (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl)
    (nativeCollarCutoffCommutator_same_annular_field χ hχ J hu hv)

#print axioms weakCutoffCommutator_zero_of_derivative_support
#print axioms nativePhysicalShellSource_eq_physicalCutoff
#print axioms nativeCollarCutoffCommutator_physical_identity
end Yamabe3.Analysis.SpherePolar
