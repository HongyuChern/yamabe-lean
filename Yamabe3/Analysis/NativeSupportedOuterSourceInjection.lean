import Yamabe3.Analysis.NativeSupportedSourcePairSpace

/-! Actual bounded injection of a lower-supported full angular source
into the SAME complete two-sided source-pair space, with zero inner source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology
namespace Yamabe3.Analysis.SpherePolar
open Delaunay
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def nativeSupportedOuterSourceInjection (b:ℝ)
    (T:X →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hT:∀x:X,∀ᵐt:ℝ∂volume,t < b → T x t=0) :
    X →L[ℝ] nativeSupportedSourcePairSpace b :=
  ((0:X →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ)).prod T).codRestrict
    (nativeSupportedSourcePairSpace b) (fun x=>(nativeSupportedSourcePairSpace_mem_iff b _).mpr (hT x))

theorem nativeSupportedOuterSourceInjection_val (b:ℝ)
    (T:X →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hT:∀x:X,∀ᵐt:ℝ∂volume,t < b → T x t=0) (x:X) :
    (nativeSupportedOuterSourceInjection b T hT x).val=(0,T x) := rfl

theorem nativeSupportedOuterSourceInjection_norm (b:ℝ)
    (T:X →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ))
    (hT:∀x:X,∀ᵐt:ℝ∂volume,t < b → T x t=0) :
    ‖nativeSupportedOuterSourceInjection b T hT‖ ≤ ‖T‖ := by
  apply (nativeSupportedOuterSourceInjection b T hT).opNorm_le_bound (norm_nonneg T)
  intro x
  change ‖((0:Lp AngularSpectralSpace 2 (volume:Measure ℝ)),T x)‖ ≤ _
  rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
  exact T.le_opNorm x

#print axioms nativeSupportedOuterSourceInjection_val
#print axioms nativeSupportedOuterSourceInjection_norm
end Yamabe3.Analysis.SpherePolar
