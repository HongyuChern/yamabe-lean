import Yamabe3.Analysis.NativeC1OffZeroSphereGreen

/-! Actual self-adjoint conformal testing for a compact C1 field which
is C2 off zero and has a genuine locally integrable density Laplacian.
No weak equation is inserted as a hypothesis and no point distribution
is discarded without the proved countable-exception Green identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic EuclideanSphereTrace GreenParametrix

theorem native_compact_C2_laplacian_selfadjoint
    (g:RiemannianMetric 3 E) (u:nativeC2OffZero) (hu:ContDiff ℝ 1 u.val) (huc:HasCompactSupport u.val)
    (hl:LocallyIntegrable (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x) volume)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) :
    (∫x,u.val x*g.leviCivitaData.laplacian φ x ∂g.volumeMeasure)=
      ∫x,φ x*g.leviCivitaData.laplacian u.val x ∂g.volumeMeasure := by
  have h₁:=NativeC1Green.integral_mul_laplacian_of_compact_C1_test g.leviCivitaData hu.contMDiff hφ.contMDiff huc
  have h₂:=nativeC1OffZero_compact_green g u hu hl (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hc
  apply h₁.trans
  apply Eq.trans _ h₂.symm
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x=>g.symm x _ _)

theorem native_compact_C2_conformal_transposed
    (g:RiemannianMetric 3 E) (u:nativeC2OffZero) (hu:ContDiff ℝ 1 u.val) (huc:HasCompactSupport u.val)
    (hl:LocallyIntegrable (fun x=>g.pullbackVolumeDensity id x*g.leviCivitaData.laplacian u.val x) volume)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) :
    (∫x,u.val x*(-8*g.leviCivitaData.laplacian φ x+g.leviCivitaData.scalarCurvature x*φ x) ∂g.volumeMeasure)=
      ∫x,(-8*g.leviCivitaData.laplacian u.val x+g.leviCivitaData.scalarCurvature x*u.val x)*φ x ∂g.volumeMeasure := by
  have he:=native_compact_C2_laplacian_selfadjoint g u hu huc hl φ hφ hc
  have hi₁:Integrable (fun x=>u.val x*g.leviCivitaData.laplacian φ x) g.volumeMeasure:=
    NativeC1Green.integrable_mul_laplacian_C1 g.leviCivitaData hu.contMDiff hφ.contMDiff huc
  have hi₂:Integrable (fun x=>φ x*g.leviCivitaData.laplacian u.val x) g.volumeMeasure:=
    nativeC1OffZero_mul_laplacian_integrable g u hl hφ.continuous hc
  have hiR:Integrable (fun x=>g.leviCivitaData.scalarCurvature x*u.val x*φ x) g.volumeMeasure:=
    ((g.leviCivitaData.contMDiff_scalarCurvature.continuous.mul hu.continuous).mul hφ.continuous).integrable_of_hasCompactSupport
      (huc.mul_left.mul_right)
  calc
    _ = ∫x,(-8:ℝ)*(u.val x*g.leviCivitaData.laplacian φ x)+
        g.leviCivitaData.scalarCurvature x*u.val x*φ x ∂g.volumeMeasure:=by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x=>by ring)
    _ = (-8:ℝ)*(∫x,u.val x*g.leviCivitaData.laplacian φ x ∂g.volumeMeasure)+
        ∫x,g.leviCivitaData.scalarCurvature x*u.val x*φ x ∂g.volumeMeasure:=by
      rw [integral_add (hi₁.const_mul _) hiR,integral_const_mul]
    _ = (-8:ℝ)*(∫x,φ x*g.leviCivitaData.laplacian u.val x ∂g.volumeMeasure)+
        ∫x,g.leviCivitaData.scalarCurvature x*u.val x*φ x ∂g.volumeMeasure:=by rw [he]
    _ = ∫x,(-8:ℝ)*(φ x*g.leviCivitaData.laplacian u.val x)+
        g.leviCivitaData.scalarCurvature x*u.val x*φ x ∂g.volumeMeasure:=by
      rw [integral_add (hi₂.const_mul _) hiR,integral_const_mul]
    _ = _:=by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x=>by ring)

#print axioms native_compact_C2_laplacian_selfadjoint
#print axioms native_compact_C2_conformal_transposed
end Yamabe3.Analysis.SpherePolar
