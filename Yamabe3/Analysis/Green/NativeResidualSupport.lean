import Yamabe3.Analysis.Green.NativeLocalParametrix

/-! Support and measurability of the explicit native residual, for its
actual chart extension back to the original manifold. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open Yamabe3.Parametrix

theorem tsupport_singularCutoffError_subset (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) :
    tsupport (singularCutoffError g χ) ⊆ tsupport χ := by
  unfold singularCutoffError
  apply (tsupport_add (f := _) (g := _)).trans
  apply union_subset
  · apply tsupport_mul_subset_left.trans
    change tsupport (- (g.leviCivitaData.laplacian χ)) ⊆ tsupport χ
    rw [tsupport_neg]
    exact g.leviCivitaData.tsupport_laplacian_subset χ
  · apply tsupport_mul_subset_left.trans
    exact g.leviCivitaData.tsupport_inner_gradient_subset_left χ radialQuadratic

theorem tsupport_nativeResidual_subset (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) :
    tsupport (nativeResidual g χ) ⊆ tsupport χ := by
  unfold nativeResidual
  exact (tsupport_add (f := _) (g := _)).trans
    (union_subset tsupport_mul_subset_left (tsupport_singularCutoffError_subset g χ))

theorem measurable_nativeResidual (g : RiemannianMetric 3 E)
    (χ : ContDiffBump (0 : E)) : Measurable (nativeResidual g χ) := by
  have hρ := native_density_smooth_positive g
  have hD : ContDiff ℝ ∞ (fderiv ℝ (g.pullbackVolumeDensity id)) :=
    hρ.1.fderiv_right (by simp)
  have hm : Measurable (densityResidual (g.pullbackVolumeDensity id)
      (fun x => g.leviCivitaData.scalarCurvature x / 8)) := by
    unfold densityResidual
    exact (((hD.continuous.clm_apply continuous_id).measurable.div
      (hρ.1.continuous.measurable.mul (measurable_norm.pow_const 3))).add
      ((g.leviCivitaData.continuous_scalarCurvature.div_const 8).measurable.div measurable_norm))
  exact (χ.continuous.measurable.mul hm).add
    (continuous_singularCutoffError g χ).measurable

#print axioms tsupport_nativeResidual_subset
#print axioms measurable_nativeResidual

end Yamabe3.Analysis.GreenParametrix
