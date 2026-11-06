import Yamabe3.Analysis.NativePrincipalErrorRows

/-! Continuity of the actual geometric error on the punctured entrance
collar, obtained from the retained C2 representative. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay Poincare.Analysis.Elliptic.Iteration
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem nativePrincipalError_continuousOn (g : RiemannianMetric 3 E) (ε : ℝ)
    {u : E → ℝ} {W : Set E} (hW : IsOpen W) (hu : ContDiffOn ℝ 2 u W) :
    ContinuousOn (nativePrincipalError g ε u) W := by
  have hpartial (j : Fin 3) : ContDiffOn ℝ 1 (partialDeriv j u) W :=
    (hu.fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const
  have hsecond (i j : Fin 3) : ContinuousOn (partialDeriv i (partialDeriv j u)) W := by
    have hh : ContDiffOn ℝ 0 (partialDeriv i (partialDeriv j u)) W :=
      ((hpartial j).fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const
    exact hh.continuousOn
  have hc : ContinuousOn (nativeScaledGeometricError g ε u) W := by
    unfold nativeScaledGeometricError secondOrderPerturbation
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ =>
          (contDiff_nativeScaledPrincipalError g ε i j).continuous.continuousOn.mul (hsecond i j)))
      · exact continuousOn_finset_sum _ (fun j _ =>
          (contDiff_nativeScaledFirstError g ε j).continuous.continuousOn.mul (hpartial j).continuousOn)
    · exact continuousOn_const.mul hu.continuousOn
  exact hc.congr (fun x hx => nativePrincipalError_eq_classical g ε (hu.contDiffAt (hW.mem_nhds hx)))

theorem nativeNormalizedPrincipalError_entrance_continuous
    (g : RiemannianMetric 3 E) (ε : ℝ) (v : HalfEndPhysicalH4Graph) :
    Continuous (fun x : HalfEndSourceEntrance => nativeNormalizedPrincipalError g ε
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x) := by
  let W : Set E := ball (0:E) 4 \ {(0:E)}
  have hW : IsOpen W := isOpen_ball.sdiff isClosed_singleton
  have hu := halfEndPhysicalH4Graph_contDiffOn_two v
  have hP := nativePrincipalError_continuousOn g ε hW hu
  have hρ : ContinuousOn (fun x : E => radialScale ‖x‖) W := by
    unfold radialScale
    apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div_const
    apply ContinuousOn.neg
    exact continuous_norm.continuousOn.log (fun x hx => norm_ne_zero_iff.mpr hx.2)
  have h := hP.div hρ (fun x _ => (radialScale_pos ‖x‖).ne')
  apply h.comp_continuous continuous_subtype_val
  intro x
  exact ⟨by simpa only [mem_ball,dist_zero_right] using lt_of_le_of_lt x.2.2 (by norm_num : (3:ℝ)<4), x.2.1⟩

#print axioms nativePrincipalError_continuousOn
#print axioms nativeNormalizedPrincipalError_entrance_continuous
end Yamabe3.Analysis.UniformElliptic
