import Yamabe3.Analysis.NativeH4FiniteWindowGeometricSource
import Yamabe3.Analysis.NativeSupportedSourcePairSpace

/-! The actual original-H4 near residual lands in the SAME complete
lower-supported source-pair space used by the full negative feedback.
This support is proved from the actual finite shell returns. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
variable (P:NativeHighPotential)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  {τ:ℝ} (ht:0 < τ) (m:ℕ) (gE:RiemannianMetric 3 E) (a b:ℝ)
  (hb:b ≤ -(m:ℝ)/2-1)

include hb in
theorem nativeH4FiniteWindowGlobalSource_supported (x:HalfEndPhysicalH4Graph) :
    nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a x∈nativeSupportedSourcePairSpace b := by
  apply (nativeSupportedSourcePairSpace_mem_iff b _).mpr
  have hh:=nativeFiniteOuterWindowSource_lower_support m
    (fun i=>nativeH4FiniteWindowGeometricRowCLM P ht gE a i) x
  filter_upwards [hh] with t h
  exact fun ht=>h (ht.trans_le hb)

def nativeH4SupportedWindowSourceCLM : HalfEndPhysicalH4Graph →L[ℝ] nativeSupportedSourcePairSpace b :=
  (nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a).codRestrict
    (nativeSupportedSourcePairSpace b) (nativeH4FiniteWindowGlobalSource_supported P hp ht m gE a b hb)

theorem nativeH4SupportedWindowSource_val (x:HalfEndPhysicalH4Graph) :
    (nativeH4SupportedWindowSourceCLM P hp ht m gE a b hb x).val=
      nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a x := rfl

theorem nativeH4SupportedWindowSource_norm :
    ‖nativeH4SupportedWindowSourceCLM P hp ht m gE a b hb‖ ≤
      ‖nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a‖ := by
  apply (nativeH4SupportedWindowSourceCLM P hp ht m gE a b hb).opNorm_le_bound (norm_nonneg _)
  intro x
  exact (nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a).le_opNorm x

#print axioms nativeH4FiniteWindowGlobalSource_supported
#print axioms nativeH4SupportedWindowSource_val
#print axioms nativeH4SupportedWindowSource_norm
end Yamabe3.Analysis.UniformElliptic
