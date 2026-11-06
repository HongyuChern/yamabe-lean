import Yamabe3.Analysis.Cylinder.NativeCylinderLift
import GreenMass.NativeSphereArea
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual native sphere area and logarithmic polar volume

The angular measure is identified with the volume of the induced round
metric. The radial Jacobian r² comes from the measure-preserving genuine
polar homeomorphism, and the substitution r = exp(-t) is the actual
one-dimensional Jacobian theorem. No polar volume formula is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Yamabe3.Analysis.SpherePolar

open Poincare.Geometry.Riemannian.SpaceForm

abbrev angularVolume : Measure S := (roundSphereMetric 2).volumeMeasure

theorem polar_sphereMeasure_eq_native :
    (volume : Measure E).toSphere = angularVolume := by
  have hmetric : GreenMass.NativeSphereGeometry.sphereMetric = roundSphereMetric 2 := rfl
  exact GreenMass.NativeSphereArea.sphereArea_eq_native_area.trans
    (congrArg (fun g => g.volumeMeasure) hmetric)

theorem measurePreserving_native_polar :
    MeasurePreserving (homeomorphUnitSphereProd E)
      ((volume : Measure E).comap (Subtype.val : ({(0 : E)}ᶜ : Set E) → E))
      (angularVolume.prod (Measure.volumeIoiPow 2)) := by
  simpa only [polar_sphereMeasure_eq_native, E, finrank_euclideanSpace, Fintype.card_fin,
    Nat.reduceSub] using (volume : Measure E).measurePreserving_homeomorphUnitSphereProd

theorem integrable_euclidean_iff_polar (f : E → ℝ) :
    Integrable f ↔ Integrable (fun p : S × Ioi (0 : ℝ) => f (p.2.1 • (p.1 : E)))
      (angularVolume.prod (Measure.volumeIoiPow 2)) := by
  have hinv (x : ({(0 : E)}ᶜ : Set E)) :
      (((homeomorphUnitSphereProd E) x).2 : ℝ) • (((homeomorphUnitSphereProd E) x).1 : E) = (x : E) := by
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using
      congrArg (fun y : ({(0 : E)}ᶜ : Set E) => (y : E))
        ((homeomorphUnitSphereProd E).symm_apply_apply x)
  have h := measurePreserving_native_polar.integrable_comp_emb
    (Homeomorph.measurableEmbedding _)
    (g := fun p => f ((homeomorphUnitSphereProd E).symm p))
  simp only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe, hinv] at h
  rw [← restrict_compl_singleton (μ := (volume : Measure E)) 0,
    ← IntegrableOn, integrableOn_iff_comap_subtypeVal (isClosed_singleton.measurableSet.compl)]
  simpa only [Function.comp_def] using h

theorem integral_native_polar (f : E → ℝ) (hf : Integrable f) :
    (∫ x : E, f x) = ∫ θ : S, ∫ r : Ioi (0 : ℝ), f (r.1 • (θ : E))
      ∂Measure.volumeIoiPow 2 ∂angularVolume := by
  calc
    _ = ∫ x : ({(0 : E)}ᶜ : Set E), f x ∂((volume : Measure E).comap Subtype.val) := by
      rw [integral_subtype_comap (isClosed_singleton.measurableSet.compl),
        restrict_compl_singleton]
    _ = ∫ p : S × Ioi (0 : ℝ), f (p.2.1 • (p.1 : E))
        ∂(angularVolume.prod (Measure.volumeIoiPow 2)) := by
      simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] using
        measurePreserving_native_polar.integral_comp (Homeomorph.measurableEmbedding _)
          (fun p => f ((homeomorphUnitSphereProd E).symm p))
    _ = _ := integral_prod _ ((integrable_euclidean_iff_polar f).mp hf)

theorem integral_radius_density (g : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), g r ∂Measure.volumeIoiPow 2) =
      ∫ r in Ioi (0 : ℝ), r ^ 2 * g r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    ((measurable_subtype_coe.pow_const 2).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r ^ 2) • g r)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  change Real.toNNReal (r ^ 2) • g r = r ^ 2 * g r
  rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg r), smul_eq_mul]

theorem integrable_radius_density_iff (g : ℝ → ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) => g r) (Measure.volumeIoiPow 2) ↔
      IntegrableOn (fun r : ℝ => r ^ 2 * g r) (Ioi 0) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (by simp), integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  simp only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem image_exp_neg_univ : (fun t : ℝ => Real.exp (-t)) '' univ = Ioi 0 := by
  ext r
  constructor
  · rintro ⟨t, _, rfl⟩
    exact Real.exp_pos _
  · intro hr
    refine ⟨-Real.log r, mem_univ _, ?_⟩
    change Real.exp (-(-Real.log r)) = r
    rw [neg_neg, Real.exp_log hr]

theorem integral_exp_neg (g : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), g r) = ∫ t : ℝ, Real.exp (-t) * g (Real.exp (-t)) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using ((hasDerivAt_id t).neg.exp)
  have hi : InjOn (fun t : ℝ => Real.exp (-t)) univ := by
    intro s _ t _ h
    exact neg_injective (Real.exp_injective h)
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hd t).hasDerivWithinAt) hi g
  simpa only [image_exp_neg_univ, setIntegral_univ, abs_neg,
    abs_of_pos (Real.exp_pos _), smul_eq_mul] using h

theorem integrable_exp_neg_iff (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔
      Integrable (fun t : ℝ => Real.exp (-t) * g (Real.exp (-t))) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using ((hasDerivAt_id t).neg.exp)
  have hi : InjOn (fun t : ℝ => Real.exp (-t)) univ := by
    intro s _ t _ h
    exact neg_injective (Real.exp_injective h)
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hd t).hasDerivWithinAt) hi g
  simpa only [image_exp_neg_univ, integrableOn_univ, abs_neg,
    abs_of_pos (Real.exp_pos _), smul_eq_mul] using h

theorem exp_polar_jacobian (t : ℝ) :
    Real.exp (-t) * Real.exp (-t) ^ 2 = Real.exp (-3 * t) := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem integral_radius_log (g : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), g r ∂Measure.volumeIoiPow 2) =
      ∫ t : ℝ, Real.exp (-3 * t) * g (Real.exp (-t)) := by
  rw [integral_radius_density, integral_exp_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [← mul_assoc, exp_polar_jacobian]

theorem integrable_radius_log_iff (g : ℝ → ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) => g r) (Measure.volumeIoiPow 2) ↔
      Integrable (fun t : ℝ => Real.exp (-3 * t) * g (Real.exp (-t))) := by
  rw [integrable_radius_density_iff, integrable_exp_neg_iff]
  have he : (fun t : ℝ => Real.exp (-t) * (Real.exp (-t) ^ 2 * g (Real.exp (-t)))) =
      fun t => Real.exp (-3 * t) * g (Real.exp (-t)) := by
    funext t
    rw [← mul_assoc, exp_polar_jacobian]
  rw [he]

#print axioms measurePreserving_native_polar
#print axioms integral_native_polar
#print axioms integral_radius_log
#print axioms integrable_radius_log_iff

end Yamabe3.Analysis.SpherePolar
