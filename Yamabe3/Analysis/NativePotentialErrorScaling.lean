import Yamabe3.Analysis.NativePrincipalErrorScaling
import Yamabe3.Analysis.UniformElliptic.NativeDelaunayPotentialError
import Yamabe3.Analysis.WeakLocalMultiplierExplicit

/-! Exact scaling of the scalar-curvature and density/potential defect.
The shifted Delaunay phase and the source normalization are explicit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem nativeDelaunayPotentialError_scale (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ → ℝ) (τ : ℝ) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ≠ 0) :
    r^2*nativeDelaunayPotentialError g ε v τ (r • x) =
      nativeDelaunayPotentialError g (ε*r) v (τ-Real.log r) x := by
  unfold nativeDelaunayPotentialError annularDelaunayPotential
  rw [smul_smul,norm_smul,Real.norm_of_nonneg hr.le,Real.log_mul hr.ne' (norm_pos_iff.mpr hx).ne']
  rw [show τ-(Real.log r+Real.log ‖x‖)=τ-Real.log r-Real.log ‖x‖ by ring]
  field_simp [hr.ne',norm_ne_zero_iff.mpr hx]
  <;> ring

def nativeNormalizedPotentialError (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ → ℝ) (τ : ℝ) (u : E → ℝ) : E → ℝ :=
  fun x => nativeDelaunayPotentialError g ε v τ x*u x /radialScale ‖x‖

theorem nativeNormalizedPotentialError_slice (g : RiemannianMetric 3 E) (ε s : ℝ)
    (v : ℝ → ℝ) (τ : ℝ) (u : E → ℝ) {x : E} (hx : x ≠ 0) :
    radialScale ‖x‖*nativeNormalizedPotentialError g ε v τ u (Real.exp (-s) • x) =
      nativeDelaunayPotentialError g (ε*Real.exp (-s)) v (τ+s) x *
        (Real.exp (3*s/2)*u (Real.exp (-s) • x)) := by
  have hs := nativeDelaunayPotentialError_scale g ε v τ (Real.exp_pos (-s)) hx
  rw [Real.log_exp,sub_neg_eq_add] at hs
  rw [← hs]
  unfold nativeNormalizedPotentialError
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,
    radialScale_mul_positive (Real.exp_pos _) (norm_pos_iff.mpr hx)]
  have ha : (radialScale (Real.exp (-s)))⁻¹ = Real.exp (-s/2) := by
    unfold radialScale
    rw [Real.log_exp,← Real.exp_neg]
    congr 1
    ring
  have he : Real.exp (3*s/2)*Real.exp (-s)^2 = Real.exp (-s/2) := by
    rw [pow_two,← mul_assoc,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  rw [div_eq_mul_inv,mul_inv_rev,ha,← he]
  field_simp [(radialScale_pos ‖x‖).ne']
  <;> ring

#print axioms nativeDelaunayPotentialError_scale
#print axioms nativeNormalizedPotentialError_slice
end Yamabe3.Analysis.UniformElliptic
