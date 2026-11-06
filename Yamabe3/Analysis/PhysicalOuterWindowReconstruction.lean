import Yamabe3.Analysis.PhysicalL2OuterWindowSource
import Yamabe3.Analysis.PhysicalOuterWindowGeometry

/-! Exact physical reconstruction of a real restricted L2 source over
the finite outer window. The source is not replaced by its high-mode
projection; the radial weight and determinant cancel explicitly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay

theorem physicalL2ScaledCollar_pair_integral (O:Set E) (hO:MeasurableSet O)
    (s:ℝ) (hs:s ≤ 0) (U:Lp ℝ 2 (volume.restrict O)) (φ:E→ℝ) :
    Real.exp (-5*s/2)*(∫y in nativeSourceShell,physicalL2ScaledCollarCLM O hO s hs U y*
      φ (Real.exp (-s) • y))=
        ∫x in nativeScaledSourceShell s,O.indicator (U:E→ℝ) x*φ x := by
  have hμ:volume.restrict nativeSourceShell ≤ volume.restrict nativePoissonEntranceCollar :=
    Measure.restrict_mono nativeSourceShell_subset_collar le_rfl
  have he:(∫y in nativeSourceShell,physicalL2ScaledCollarCLM O hO s hs U y*φ (Real.exp (-s) • y))=
      Real.exp (-s/2)*(∫y in nativeSourceShell,O.indicator (U:E→ℝ) (Real.exp (-s) • y)*φ (Real.exp (-s) • y)) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_mono hμ (physicalL2ScaledCollarCLM_ae O hO s hs U)] with y hy
    rw [hy]
    ring
  rw [he]
  have hd:=setIntegral_comp_dilation (Real.exp_ne_zero (-s)) (nativeScaledSourceShell s)
    (fun x=>O.indicator (U:E→ℝ) x*φ x)
  rw [nativeScaledSourceShell_inverse_preimage] at hd
  simp only [finrank_euclideanSpace_fin,←Real.exp_nat_mul,←Real.exp_neg,abs_of_pos (Real.exp_pos _)] at hd
  rw [hd]
  have hf:Real.exp (-5*s/2)*Real.exp (-s/2)*Real.exp (-(-s*3))=1 := by
    rw [←Real.exp_add,←Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  calc
    _=(Real.exp (-5*s/2)*Real.exp (-s/2)*Real.exp (-(-s*3)))*
        (∫x in nativeScaledSourceShell s,O.indicator (U:E→ℝ) x*φ x) := by ring
    _=_ := by rw [hf,one_mul]

theorem physicalL2OuterWindowSource_physical_test (O:Set E) (hO:MeasurableSet O) (m:ℕ)
    (U:Lp ℝ 2 (volume.restrict O)) (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ)
    (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ) :
    inner ℝ (physicalL2OuterWindowSourceCLM O hO m U) (nativePhysicalPairTestL2 φ hφ hc h0)=
      ∫x in nativePolarTimeWindow (Ioc (-(m:ℝ)/2) 0),O.indicator (U:E→ℝ) x*φ x := by
  have hm:MemLp (O.indicator (U:E→ℝ)) 2 (volume:Measure E) :=
    (memLp_indicator_iff_restrict hO).mpr (Lp.memLp U)
  have hp:MemLp φ 2 (volume:Measure E) := hφ.continuous.memLp_of_hasCompactSupport hc
  have hi:Integrable (fun x:E=>O.indicator (U:E→ℝ) x*φ x) := hm.integrable_mul hp
  rw [show physicalL2OuterWindowSourceCLM O hO m=
    nativeFiniteOuterWindowSourceCLM m (fun i=>physicalL2ScaledCollarCLM O hO
      (nativeOuterLogShellCenter i) (by dsimp only [nativeOuterLogShellCenter];have hi:0 ≤ (i.val:ℝ):=Nat.cast_nonneg _;linarith)) from rfl]
  rw [nativeFiniteOuterWindowSource_physical_test _ _ _ _ hφ hc h0]
  simp_rw [physicalL2ScaledCollar_pair_integral]
  rw [←nativeScaledOuterWindow_union]
  exact (integral_iUnion_fintype (fun i:Fin m=>nativeScaledSourceShell_measurable (nativeOuterLogShellCenter i))
    (nativeScaledOuterShell_disjoint m) (fun _=>hi.integrableOn)).symm

#print axioms physicalL2ScaledCollar_pair_integral
#print axioms physicalL2OuterWindowSource_physical_test
end Yamabe3.Analysis.SpherePolar
