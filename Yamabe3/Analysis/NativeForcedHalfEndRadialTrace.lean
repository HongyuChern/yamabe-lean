import Yamabe3.Analysis.NativeForcedHalfEndDerivativeOperator
import Yamabe3.Analysis.DelaunayRadialProfile

/-!
# The actual inner radial derivative at the forced entrance

The radial Hilbert curve is literally `radialScale r • U (-log r)` for
the original native forced half-end.  Its derivative on `Ioc 0 1` is
obtained by composing the actual right derivative of that same U with
the real logarithm and the existing radial conformal factor.  At radius
one the zero Dirichlet value removes the half-value term.

Consequently the literal `-8` times inner radial derivative is a bounded
linear source map, equal to eight times the already constructed entrance
right derivative.  This is a statement about that actual Hilbert-valued
radial curve.  No manifold conormal or trace-quotient identification is
assumed, and no derivative of the negative-time extension is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

/-- The actual radial derivative uses only the actual right derivative
on nonnegative cylinder times.  The entrance is included in the domain. -/
theorem halfEnd_radialCurve_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U D : ℝ → E)
    (hU : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt U (D t) (Ici 0) t)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    HasDerivWithinAt (fun s : ℝ => radialScale s • U (-Real.log s))
      (-(radialScale r / r) • ((1 / 2 : ℝ) • U (-Real.log r) + D (-Real.log r)))
      (Ioc 0 1) r := by
  have hmap : MapsTo (fun s : ℝ => -Real.log s) (Ioc 0 1) (Ici 0) := by
    intro s hs
    exact neg_nonneg.mpr (Real.log_nonpos hs.1.le hs.2)
  have ht : 0 ≤ -Real.log r := neg_nonneg.mpr (Real.log_nonpos hr.le hr1)
  have hcomp := (hU (-Real.log r) ht).scomp r
    ((Real.hasDerivAt_log hr.ne').neg.hasDerivWithinAt) hmap
  have hprod := (radialScale_hasDerivAt hr).hasDerivWithinAt.smul hcomp
  apply hprod.congr_deriv
  have hD : radialScale r * (-r⁻¹) = -(radialScale r / r) := by
    simp only [div_eq_mul_inv, mul_neg]
  have hV : -radialScale r / (2 * r) = -(radialScale r / r) * (1 / 2 : ℝ) := by
    field_simp [hr.ne'] <;> ring
  simp only [Function.comp_apply, Pi.neg_apply, smul_add, smul_smul, hD, hV, add_comm]

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The literal Hilbert-valued radial curve of the same original solution. -/
def nativeHalfHighDirichletRadial (F : ℝ≥0 →ᵇ AngularL2) (r : ℝ) : AngularL2 :=
  radialScale r • nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F (-Real.log r)

theorem nativeHalfHighDirichletRadial_hasDerivWithinAt
    (F : ℝ≥0 →ᵇ AngularL2) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    HasDerivWithinAt (nativeHalfHighDirichletRadial hκ0 hκ1 V hV hV0 F)
      (-(radialScale r / r) •
        ((1 / 2 : ℝ) • nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F (-Real.log r) +
          nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F (-Real.log r)))
      (Ioc 0 1) r :=
  halfEnd_radialCurve_hasDerivWithinAt _ _
    (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 F) r hr hr1

theorem nativeHalfHighDirichletRadial_continuousOn (F : ℝ≥0 →ᵇ AngularL2) :
    ContinuousOn (nativeHalfHighDirichletRadial hκ0 hκ1 V hV hV0 F) (Ioc 0 1) := by
  intro r hr
  exact (nativeHalfHighDirichletRadial_hasDerivWithinAt hκ0 hκ1 V hV hV0 F r hr.1 hr.2).continuousWithinAt

theorem nativeHalfHighDirichletRadial_one (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletRadial hκ0 hκ1 V hV hV0 F 1 = 0 := by
  rw [nativeHalfHighDirichletRadial, Real.log_one, neg_zero,
    nativeHalfHighDirichletPhysical_zero_of_nonpos hκ0 hκ1 V hV hV0 F 0 le_rfl, smul_zero]

/-- Radius one uses the actual inner derivative, with the original
zero Dirichlet value.  No two-sided differentiability is asserted. -/
theorem nativeHalfHighDirichletRadial_hasDerivWithinAt_one
    (F : ℝ≥0 →ᵇ AngularL2) :
    HasDerivWithinAt (nativeHalfHighDirichletRadial hκ0 hκ1 V hV hV0 F)
      (-(nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F)) (Ioc 0 1) 1 := by
  have h := nativeHalfHighDirichletRadial_hasDerivWithinAt hκ0 hκ1 V hV hV0 F
    1 (by norm_num) le_rfl
  rw [nativeHalfHighDirichletEntranceDerivativeCLM_apply]
  simpa only [radialScale, Real.log_one, neg_zero, zero_div, Real.exp_zero, div_one,
    nativeHalfHighDirichletPhysical_zero_of_nonpos hκ0 hκ1 V hV hV0 F 0 le_rfl,
    smul_zero, zero_add, neg_one_smul] using h

/-- The literal `-8` radial derivative at radius one, as a source map. -/
def nativeHalfHighDirichletInnerRadialFluxCLM :
    (ℝ≥0 →ᵇ AngularL2) →L[ℝ] AngularL2 :=
  (8 : ℝ) • nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0

theorem nativeHalfHighDirichletInnerRadialFluxCLM_apply (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletInnerRadialFluxCLM hκ0 hκ1 V hV hV0 F =
      (8 : ℝ) • nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F 0 := by
  rw [nativeHalfHighDirichletInnerRadialFluxCLM, ContinuousLinearMap.smul_apply,
    nativeHalfHighDirichletEntranceDerivativeCLM_apply]

theorem nativeHalfHighDirichletInnerRadialFluxCLM_eq_derivWithin
    (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletInnerRadialFluxCLM hκ0 hκ1 V hV hV0 F =
      (-8 : ℝ) • derivWithin (nativeHalfHighDirichletRadial hκ0 hκ1 V hV hV0 F) (Ioc 0 1) 1 := by
  have hd := (nativeHalfHighDirichletRadial_hasDerivWithinAt_one hκ0 hκ1 V hV hV0 F).derivWithin
    (uniqueDiffOn_Ioc (0 : ℝ) 1 1 ⟨by norm_num, le_rfl⟩)
  rw [hd, nativeHalfHighDirichletInnerRadialFluxCLM, ContinuousLinearMap.smul_apply]
  simp only [neg_smul, smul_neg, neg_neg]

theorem nativeHalfHighDirichletInnerRadialFluxCLM_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletInnerRadialFluxCLM hκ0 hκ1 V hV hV0 F‖ ≤
      (8 * nativeHalfHighDirichletDerivativeBound κ V) * ‖F‖ := by
  rw [nativeHalfHighDirichletInnerRadialFluxCLM, ContinuousLinearMap.smul_apply,
    norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
  calc
    _ ≤ 8 * (nativeHalfHighDirichletDerivativeBound κ V * ‖F‖) :=
      mul_le_mul_of_nonneg_left
        (nativeHalfHighDirichletEntranceDerivativeCLM_norm_le hκ0 hκ1 V hV hV0 F) (by norm_num)
    _ = _ := by ring

theorem nativeHalfHighDirichletInnerRadialFluxCLM_source_difference
    (F G : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletInnerRadialFluxCLM hκ0 hκ1 V hV hV0 F -
      nativeHalfHighDirichletInnerRadialFluxCLM hκ0 hκ1 V hV hV0 G‖ ≤
      (8 * nativeHalfHighDirichletDerivativeBound κ V) * ‖F - G‖ := by
  rw [← map_sub]
  exact nativeHalfHighDirichletInnerRadialFluxCLM_norm_le hκ0 hκ1 V hV hV0 (F - G)

#print axioms halfEnd_radialCurve_hasDerivWithinAt
#print axioms nativeHalfHighDirichletRadial_hasDerivWithinAt_one
#print axioms nativeHalfHighDirichletInnerRadialFluxCLM_eq_derivWithin
#print axioms nativeHalfHighDirichletInnerRadialFluxCLM_source_difference

end Yamabe3.Analysis.Delaunay
