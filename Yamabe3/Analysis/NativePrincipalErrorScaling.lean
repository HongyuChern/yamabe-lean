import Yamabe3.Analysis.NativeC2GeometricError
import Yamabe3.Analysis.UniformElliptic.DivergenceScaling
import Yamabe3.Analysis.UniformElliptic.HalfEndPhysicalH2SourceGraph

/-! Exact source normalization of the actual principal error. The source
weight, divergence sign and all logarithmic slice amplitudes are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

def nativePrincipalError (g : RiemannianMetric 3 E) (ε : ℝ) (u : E → ℝ) : E → ℝ :=
  fun x => -principalSource (fun y => nativeDivergenceMatrix g (ε • y) - 1) u x

def nativeNormalizedPrincipalError (g : RiemannianMetric 3 E) (ε : ℝ) (u : E → ℝ) : E → ℝ :=
  fun x => nativePrincipalError g ε u x / radialScale ‖x‖

theorem nativePrincipalError_scaled (g : RiemannianMetric 3 E) (ε r c : ℝ)
    (u : E → ℝ) (x : E) :
    nativePrincipalError g (ε*r) (fun y => c*u (r • y)) x =
      c*r^2*nativePrincipalError g ε u (r • x) := by
  have h := principalSource_scaled_centered
    (fun y => nativeDivergenceMatrix g (ε • y) - 1) u r c 0 x
  simp only [sub_zero,smul_smul] at h
  unfold nativePrincipalError
  rw [h]
  ring

theorem nativeNormalizedPrincipalError_slice (g : RiemannianMetric 3 E) (ε s : ℝ)
    (u : E → ℝ) {x : E} (hx : x ≠ 0) :
    radialScale ‖x‖ * nativeNormalizedPrincipalError g ε u (Real.exp (-s) • x) =
      nativePrincipalError g (ε*Real.exp (-s))
        (fun y => Real.exp (3*s/2)*u (Real.exp (-s) • y)) x := by
  rw [nativePrincipalError_scaled]
  unfold nativeNormalizedPrincipalError
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
  rw [he]
  have hn : radialScale ‖x‖ ≠ 0 := (radialScale_pos _).ne'
  rw [div_eq_mul_inv,mul_inv_rev,ha]
  field_simp
  <;> ring

theorem nativePrincipalError_eq_classical (g : RiemannianMetric 3 E) (ε : ℝ)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    nativePrincipalError g ε u x = nativeScaledGeometricError g ε u x :=
  (nativeScaledGeometricError_eq_negative_principalSource_C2_at g ε x hu).symm

#print axioms nativePrincipalError_scaled
#print axioms nativeNormalizedPrincipalError_slice
#print axioms nativePrincipalError_eq_classical
end Yamabe3.Analysis.UniformElliptic
