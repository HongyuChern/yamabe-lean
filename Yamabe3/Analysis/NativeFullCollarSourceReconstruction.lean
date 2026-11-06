import Yamabe3.Analysis.NativeFullCollarSourceReturn
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Actual reconstruction of every physical collar L2 source. The
weighted adjoint is a right inverse of the real polar source lift,
as proved by compact physical tests and the fundamental lemma. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeCollarL2_eq_of_physical_tests (R U : NativeCollarL2)
    (he : ∀φ : E→ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆nativePoissonEntranceCollar →
      (∫x in nativePoissonEntranceCollar,R x*φ x)=(∫x in nativePoissonEntranceCollar,U x*φ x)) : R=U := by
  let O := nativePoissonEntranceCollar
  have hO : IsOpen O := nativePolarTimeWindow_open (1/2)
  have hR := Lp.memLp R
  have hU := Lp.memLp U
  have hsum : LocallyIntegrableOn (fun x => R x-U x) O (volume.restrict O) :=
    ((hR.sub hU).locallyIntegrable (by norm_num)).locallyIntegrableOn O
  have hz := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hsum (fun φ hφ hc hs => by
    have hp : MemLp φ 2 (volume.restrict O) := (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
    have hRp := hR.integrable_mul hp
    have hUp := hU.integrable_mul hp
    change (∫x in O,φ x*(R x-U x))=0
    calc
      _=∫x in O,R x*φ x-U x*φ x := by congr 1;funext x;ring
      _=(∫x in O,R x*φ x)-(∫x in O,U x*φ x) := integral_sub hRp hUp
      _=0 := by rw [he φ hφ hc hs];ring)
  apply Lp.ext
  filter_upwards [hz,ae_restrict_mem hO.measurableSet] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

theorem nativeFullCollarSourceReturn_right_inverse (U : NativeCollarL2) :
    nativeL2FullPhysicalSourceCLM (nativeFullCollarSourceReturnCLM U)=U := by
  apply nativeCollarL2_eq_of_physical_tests
  intro φ hφ hc hs
  have h0 : (0:E)∉tsupport φ := by
    intro h
    have hh := (hs h).1
    exact hh rfl
  exact (nativeL2FullPhysicalSource_physical_test_on_collar φ hφ hc h0
    (nativeFullCollarSourceReturnCLM U) hs).symm.trans
      (nativeFullCollarSourceReturn_physical_test φ hφ hc h0 U)

theorem nativeFullCollarSourceReturn_operator_identity :
    nativeL2FullPhysicalSourceCLM.comp nativeFullCollarSourceReturnCLM=ContinuousLinearMap.id ℝ NativeCollarL2 := by
  apply ContinuousLinearMap.ext
  intro U
  exact nativeFullCollarSourceReturn_right_inverse U

#print axioms nativeCollarL2_eq_of_physical_tests
#print axioms nativeFullCollarSourceReturn_right_inverse
#print axioms nativeFullCollarSourceReturn_operator_identity
end Yamabe3.Analysis.SpherePolar
