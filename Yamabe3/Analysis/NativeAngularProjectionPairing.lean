import Yamabe3.Analysis.NativeAngularProjections

/-! Actual orthogonality and idempotence of the native spectral angular
projections. These identify what a high-only source return discards. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

theorem nativeAngularProjection_inner (p : AngularIndex → Prop) (u v : AngularL2) :
    inner ℝ (nativeAngularProjection p u) v=inner ℝ u (nativeAngularProjection p v) := by
  classical
  rw [←angularBasis.tsum_inner_mul_inner (nativeAngularProjection p u) v,
    ←angularBasis.tsum_inner_mul_inner u (nativeAngularProjection p v)]
  apply tsum_congr
  intro i
  rw [real_inner_comm (angularBasis i) (nativeAngularProjection p u),
    nativeAngularProjection_coefficient,nativeAngularProjection_coefficient,
    real_inner_comm (angularBasis i) u]
  by_cases hi : p i <;> simp only [hi,if_pos,if_false,zero_mul,mul_zero]

theorem nativeAngularProjection_idempotent (p : AngularIndex → Prop) (u : AngularL2) :
    nativeAngularProjection p (nativeAngularProjection p u)=nativeAngularProjection p u := by
  classical
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeAngularProjection_coefficient]
  by_cases hi : p i <;> simp only [hi,if_pos,if_false]

theorem nativeAngularProjection_pairing (p : AngularIndex → Prop) (u v : AngularL2) :
    inner ℝ (nativeAngularProjection p u) (nativeAngularProjection p v)=
      inner ℝ (nativeAngularProjection p u) v := by
  rw [←nativeAngularProjection_inner,nativeAngularProjection_idempotent]

theorem nativeHighLow_orthogonal (u v : AngularL2) :
    inner ℝ (nativeHighProjection u) (nativeLowProjection v)=0 := by
  have h := nativeHighProjection_add_low v
  have h' : nativeLowProjection v=v-nativeHighProjection v := by
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  rw [h',inner_sub_right]
  change inner ℝ (nativeAngularProjection (fun i => 6≤angularEigenvalue i) u) v-
    inner ℝ (nativeAngularProjection (fun i => 6≤angularEigenvalue i) u)
      (nativeAngularProjection (fun i => 6≤angularEigenvalue i) v)=0
  rw [nativeAngularProjection_pairing,sub_self]

#print axioms nativeAngularProjection_inner
#print axioms nativeAngularProjection_idempotent
#print axioms nativeAngularProjection_pairing
#print axioms nativeHighLow_orthogonal
end Yamabe3.Analysis.Delaunay
