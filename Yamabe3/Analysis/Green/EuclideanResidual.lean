import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
# Local L² control for the three-dimensional Green parametrix

These lemmas concern the actual Euclidean volume and inverse-radius function.
They provide the integrability step needed before applying the H¹ weak inverse.
They do not assert that a normal coordinate chart or the native point-source
identity has already been constructed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal Topology ContDiff

namespace Yamabe3.Analysis.GreenParametrix

abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The square of the Newton singularity is locally integrable in dimension 3. -/
theorem integrableOn_inv_norm_sq (R : ℝ) :
    IntegrableOn (fun x : E => (‖x‖⁻¹) ^ 2) (ball 0 R) volume := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure E)
    (f := fun r : ℝ => (r⁻¹) ^ 2)]
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 R) volume :=
    integrableOn_const (hs := by simp)
  apply hconst.congr_fun _ measurableSet_Ioo
  intro r hr
  have hr0 : r ≠ 0 := ne_of_gt hr.1
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  field_simp

/-- `r⁻¹` is an actual L² function on every finite three-dimensional ball. -/
theorem memLp_inv_norm (R : ℝ) :
    MemLp (fun x : E => ‖x‖⁻¹) 2 (volume.restrict (ball 0 R)) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_norm.inv.aestronglyMeasurable)).mpr
  exact integrableOn_inv_norm_sq R

/-- An almost-everywhere inverse-radius bound supplies a legitimate L² source. -/
theorem memLp_of_le_inv_norm {f : E → ℝ} {R C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (ball 0 R)))
    (hbound : ∀ᵐ x ∂volume.restrict (ball 0 R), |f x| ≤ C * ‖x‖⁻¹) :
    MemLp f 2 (volume.restrict (ball 0 R)) := by
  apply (memLp_inv_norm R).of_le_mul hf
  simpa only [Real.norm_eq_abs, abs_inv, abs_norm] using hbound

#print axioms integrableOn_inv_norm_sq
#print axioms memLp_inv_norm
#print axioms memLp_of_le_inv_norm

/-- A bounded coordinate density preserves the L² residual estimate. -/
theorem memLp_withDensity_of_le_inv_norm {f : E → ℝ} {R C : ℝ}
    {ρ : E → ℝ≥0∞} {A : ℝ≥0∞} (hA : A ≠ (⊤ : ℝ≥0∞))
    (hρ : ∀ᵐ x ∂volume.restrict (ball 0 R), ρ x ≤ A)
    (hf : AEStronglyMeasurable f (volume.restrict (ball 0 R)))
    (hbound : ∀ᵐ x ∂volume.restrict (ball 0 R), |f x| ≤ C * ‖x‖⁻¹) :
    MemLp f 2 ((volume.restrict (ball 0 R)).withDensity ρ) := by
  have hle : (volume.restrict (ball (0 : E) R)).withDensity ρ ≤
      A • volume.restrict (ball 0 R) := by
    rw [← withDensity_const]
    exact withDensity_mono hρ
  exact ((memLp_of_le_inv_norm hf hbound).smul_measure hA).mono_measure hle

/-- The vanishing first derivative and a genuine second-derivative bound
give the first-order bound used in the normal-coordinate residual. -/
theorem norm_fderiv_le_mul_norm {ρ : E → ℝ} {R C : ℝ}
    (hR : 0 < R) (hzero : fderiv ℝ ρ 0 = 0)
    (hD : ∀ x ∈ ball (0 : E) R, DifferentiableAt ℝ (fderiv ℝ ρ) x)
    (hDD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ (fderiv ℝ ρ) x‖ ≤ C)
    {x : E} (hx : x ∈ ball 0 R) :
    ‖fderiv ℝ ρ x‖ ≤ C * ‖x‖ := by
  have h0 : (0 : E) ∈ ball 0 R := by simpa using hR
  have h := (convex_ball (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
    hD hDD h0 hx
  simpa only [hzero, sub_zero] using h

/-- The explicit radial expression for `P(1/r)` away from the origin in a
Gauss chart. Its identification with the native operator is a separate lemma. -/
def densityResidual (ρ V : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ ρ x x / (ρ x * ‖x‖ ^ 3) + V x / ‖x‖

theorem densityResidual_bound {ρ V : E → ℝ} {c C B : ℝ} {x : E}
    (hc : 0 < c) (hC : 0 ≤ C) (hρ : c ≤ ρ x)
    (hD : ‖fderiv ℝ ρ x‖ ≤ C * ‖x‖) (hV : |V x| ≤ B)
    (hx : x ≠ 0) :
    |densityResidual ρ V x| ≤ (C / c + B) * ‖x‖⁻¹ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hρpos : 0 < ρ x := hc.trans_le hρ
  have hnum : |fderiv ℝ ρ x x| ≤ C * ‖x‖ ^ 2 := by
    calc
      |fderiv ℝ ρ x x| = ‖fderiv ℝ ρ x x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ ρ x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hD hr.le
      _ = C * ‖x‖ ^ 2 := by ring
  unfold densityResidual
  calc
    |fderiv ℝ ρ x x / (ρ x * ‖x‖ ^ 3) + V x / ‖x‖| ≤
        |fderiv ℝ ρ x x / (ρ x * ‖x‖ ^ 3)| + |V x / ‖x‖| := abs_add_le _ _
    _ = |fderiv ℝ ρ x x| / (ρ x * ‖x‖ ^ 3) + |V x| / ‖x‖ := by
      congr 1
      · exact (abs_div (fderiv ℝ ρ x x) (ρ x * ‖x‖ ^ 3)).trans
          (congrArg (fun d : ℝ => |fderiv ℝ ρ x x| / d)
            (abs_of_pos (mul_pos hρpos (pow_pos hr 3))))
      · rw [abs_div, abs_of_pos hr]
    _ ≤ (C * ‖x‖ ^ 2) / (c * ‖x‖ ^ 3) + B / ‖x‖ := by
      gcongr
    _ = (C / c + B) * ‖x‖⁻¹ := by
      field_simp

/-- The normal-coordinate expression has a genuine L² representative;
the geometric assumptions here are explicitly separated from this estimate. -/
theorem densityResidual_memLp {ρ V : E → ℝ} {R c C B : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C)
    (hzero : fderiv ℝ ρ 0 = 0)
    (hD : ∀ x ∈ ball (0 : E) R, DifferentiableAt ℝ (fderiv ℝ ρ) x)
    (hDD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ (fderiv ℝ ρ) x‖ ≤ C)
    (hρ : ∀ x ∈ ball (0 : E) R, c ≤ ρ x)
    (hV : ∀ x ∈ ball (0 : E) R, |V x| ≤ B)
    (hm : AEStronglyMeasurable (densityResidual ρ V)
      (volume.restrict (ball 0 R))) :
    MemLp (densityResidual ρ V) 2 (volume.restrict (ball 0 R)) := by
  apply memLp_of_le_inv_norm hm
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0 : E))] with x hx hx0
  exact densityResidual_bound hc hC (hρ x hx)
    (norm_fderiv_le_mul_norm hR hzero hD hDD hx) (hV x hx) hx0

#print axioms memLp_withDensity_of_le_inv_norm
#print axioms norm_fderiv_le_mul_norm
#print axioms densityResidual_bound
#print axioms densityResidual_memLp

/-- Smooth positive density with vanishing first jet supplies all local
bounds and an L² radial residual, including its actual density measure. -/
theorem exists_radius_densityResidual_memLp {ρ V : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hV : Continuous V)
    (hρ0 : 0 < ρ 0) (hzero : fderiv ℝ ρ 0 = 0) :
    ∃ R : ℝ, 0 < R ∧
      MemLp (densityResidual ρ V) 2
        ((volume.restrict (ball 0 R)).withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ ρ) := hρ.fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ρ)) := hD.fderiv_right (by simp)
  let c := ρ 0 / 2
  let C := ‖fderiv ℝ (fderiv ℝ ρ) 0‖ + 1
  let B := |V 0| + 1
  let A := ρ 0 + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlow : ∀ᶠ x in 𝓝 (0 : E), c < ρ x :=
    hρ.continuous.continuousAt.eventually (Ioi_mem_nhds (by dsimp [c]; linarith))
  have hupp : ∀ᶠ x in 𝓝 (0 : E), ρ x < A :=
    hρ.continuous.continuousAt.eventually (Iio_mem_nhds (by dsimp [A]; linarith))
  have hcDD : Continuous (fun x : E => ‖fderiv ℝ (fderiv ℝ ρ) x‖) := by
    exact Continuous.norm (f := fderiv ℝ (fderiv ℝ ρ)) hDD.continuous
  have hdb : ∀ᶠ x in 𝓝 (0 : E), ‖fderiv ℝ (fderiv ℝ ρ) x‖ < C :=
    hcDD.continuousAt.eventually
      (Iio_mem_nhds (show ‖fderiv ℝ (fderiv ℝ ρ) 0‖ < C by dsimp [C]; linarith))
  have hvb : ∀ᶠ x in 𝓝 (0 : E), |V x| < B :=
    hV.abs.continuousAt.eventually
      (Iio_mem_nhds (show |V 0| < B by dsimp [B]; linarith))
  have hall : ∀ᶠ x in 𝓝 (0 : E), c < ρ x ∧ ρ x < A ∧
      ‖fderiv ℝ (fderiv ℝ ρ) x‖ < C ∧ |V x| < B := by
    filter_upwards [hlow, hupp, hdb, hvb] with x hx1 hx2 hx3 hx4
    exact ⟨hx1, hx2, hx3, hx4⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hm : Measurable (densityResidual ρ V) := by
    unfold densityResidual
    exact (((hD.continuous.clm_apply continuous_id).measurable.div
      (hρ.continuous.measurable.mul (measurable_norm.pow_const 3))).add
        (hV.measurable.div measurable_norm))
  refine ⟨R, hR, memLp_withDensity_of_le_inv_norm
    (A := ENNReal.ofReal A) (C := C / c + B)
    ENNReal.ofReal_ne_top ?_ hm.aestronglyMeasurable ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact ENNReal.ofReal_le_ofReal (hball hx).2.1.le
  · filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : E))] with x hx hx0
    exact densityResidual_bound hc hC (hball hx).1.le
      (norm_fderiv_le_mul_norm hR hzero
        (fun y _ => hD.differentiable (by simp) y)
        (fun y hy => (hball hy).2.2.1.le) hx)
      (hball hx).2.2.2.le hx0

#print axioms exists_radius_densityResidual_memLp

end Yamabe3.Analysis.GreenParametrix
