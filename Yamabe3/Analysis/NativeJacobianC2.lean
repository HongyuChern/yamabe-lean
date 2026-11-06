import Yamabe3.Analysis.NativeDivergenceC2
import Yamabe3.Analysis.NativeGeometricSourceSolver

/-! The actual C2 solved field has the retained Levi-Civita Jacobian,
with exact radius, density, phase and factor eight. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem nativeRescaledDelaunayJacobian_eq_actual_native_jacobian_C2
    (g:RiemannianMetric 3 E3) (v:ℝ→ℝ) (σ:ℝ)
    {r:ℝ} (hr:0<r) {w:E3→ℝ} {z:E3}
    (hw:ContDiffAt ℝ 2 w (r • z)) (hz:z≠0) :
    nativeRescaledDelaunayJacobian g r v (σ-Real.log r) (fun y=>w (r • y)) z=
      (r^2*g.pullbackVolumeDensity id (r • z)/8)*
        (-8*g.leviCivitaData.laplacian w (r • z)+
          (g.leviCivitaData.scalarCurvature (r • z)-
            30*radialProfile v σ ‖r • z‖^4)*w (r • z)) := by
  have hs:principalSource (fun y=>nativeDivergenceMatrix g (r • y))
      (fun y=>w (r • y)) z=r^2*principalSource (nativeDivergenceMatrix g) w (r • z):=by
    simpa only [sub_zero,one_mul] using
      principalSource_scaled_centered (nativeDivergenceMatrix g) w r 1 0 z
  rw [nativeRescaledDelaunayJacobian,hs,
    native_principalSource_eq_negative_density_laplacian_C2 g g.leviCivitaData hw,
    rescaledNativeJacobianPotential,
    delaunayRescaledBackground_eq_physical_radialProfile v σ hr hz]
  ring

theorem native_same_scaled_field_actual_jacobian
    (g:RiemannianMetric 3 E3) (v:ℝ→ℝ) (τ:ℝ)
    {r:ℝ} (hr:0<r) {F:E3→ℝ} {x:E3}
    (hF:ContDiffAt ℝ 2 F x) (hx:x≠0) :
    nativeRescaledDelaunayJacobian g r v τ F x=
      (r^2*g.pullbackVolumeDensity id (r • x)/8)*
        (-8*g.leviCivitaData.laplacian (fun y=>F (r⁻¹ • y)) (r • x)+
          (g.leviCivitaData.scalarCurvature (r • x)-
            30*radialProfile v (τ+Real.log r) ‖r • x‖^4)*F x) := by
  have hw:ContDiffAt ℝ 2 (fun y=>F (r⁻¹ • y)) (r • x):=by
    apply ContDiffAt.comp (r • x) _ (contDiff_id.const_smul r⁻¹).contDiffAt
    simpa only [id_eq,smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using hF
  have he:(fun y:E3=>F (r⁻¹ • (r • y)))=F:=by
    funext y
    simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  have h:=nativeRescaledDelaunayJacobian_eq_actual_native_jacobian_C2 g v
    (τ+Real.log r) hr hw hx
  simpa only [add_sub_cancel_right,he,smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using h

#print axioms nativeRescaledDelaunayJacobian_eq_actual_native_jacobian_C2
#print axioms native_same_scaled_field_actual_jacobian
end Yamabe3.Analysis.UniformElliptic
