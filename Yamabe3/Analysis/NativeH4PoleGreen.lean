import Yamabe3.Analysis.NativeH4DensityLaplacianIntegrability
import Yamabe3.Analysis.NativeC1PunctureGreen

/-! Compact native Green identity for the same all-scale H4 graph field.
The point is removed using proved C1 regularity and proved local L1
classical Laplacian, without any extra weak equation or integrability. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal ContDiff Topology Manifold
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar EuclideanSphereTrace GreenParametrix
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem nativeH4Graph_mul_laplacian_integrable
    (g:RiemannianMetric 3 E) (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    {φ:E→ℝ} (hφ:Continuous φ) (hc:HasCompactSupport φ) :
    Integrable (fun x=>φ x*g.leviCivitaData.laplacian u.val x) g.volumeMeasure := by
  apply (native_integrable_iff_density g _).mpr
  have hi:=(nativeH4Graph_density_laplacian_locallyIntegrable g v u h0 hu).integrable_smul_left_of_hasCompactSupport hφ hc
  apply hi.congr
  exact Eventually.of_forall fun x=>by simp only [smul_eq_mul];ring

theorem nativeH4Graph_gradient_test_integrable
    (g:RiemannianMetric 3 E) (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (hc:HasCompactSupport φ) :
    Integrable (fun x=>g.inner x (g.leviCivitaData.gradient φ x)
      (g.leviCivitaData.gradient u.val x)) g.volumeMeasure := by
  have huc:=(nativeH4Graph_representative_C1 v u h0 hu).1
  have he:(fun x=>g.inner x (g.leviCivitaData.gradient φ x)
      (g.leviCivitaData.gradient u.val x))=
      fun x=>fderiv ℝ φ x (g.leviCivitaData.gradient u.val x):=by
    funext x
    rw [g.leviCivitaData.inner_gradient]
    simp +instances only [mvfderiv,mfderiv_eq_fderiv,NormedSpace.fromTangentSpace]
    rfl
  have hcont:Continuous (fun x=>g.inner x (g.leviCivitaData.gradient φ x)
      (g.leviCivitaData.gradient u.val x)):=by
    rw [he]
    exact (hφ.continuous_fderiv (by norm_num)).clm_apply (continuous_native_gradient_C1 g huc)
  exact hcont.integrable_of_hasCompactSupport (g.leviCivitaData.hasCompactSupport_inner_gradient hc _)

theorem nativeH4Graph_compact_green
    (g:RiemannianMetric 3 E) (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero)
    (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (hc:HasCompactSupport φ) :
    (∫x,φ x*g.leviCivitaData.laplacian u.val x ∂g.volumeMeasure)=
    -(∫x,g.inner x (g.leviCivitaData.gradient φ x) (g.leviCivitaData.gradient u.val x) ∂g.volumeMeasure) := by
  apply integral_native_mul_laplacian_off_countable g
    (nativeH4Graph_representative_C1 v u h0 hu).1 (countable_singleton (0:E))
    (fun x hx=>u.property.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)) hφ hc
  exact (native_integrable_iff_density g _).mp
    (nativeH4Graph_mul_laplacian_integrable g v u h0 hu hφ.continuous hc)

#print axioms nativeH4Graph_mul_laplacian_integrable
#print axioms nativeH4Graph_gradient_test_integrable
#print axioms nativeH4Graph_compact_green
end Yamabe3.Analysis.UniformElliptic
