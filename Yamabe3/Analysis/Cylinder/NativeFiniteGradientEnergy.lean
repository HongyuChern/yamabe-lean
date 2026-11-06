import Yamabe3.Analysis.Cylinder.NativeFiniteForcingBounds

/-!
# Genuine finite-mode Caccioppoli energy on physical annuli

The finite angular representatives solve the actual native Euclidean
Jacobi equation. Their norm-one spectral projections give genuine shell
L2 bounds. The actual identity principal form and constructed compact
extensions therefore yield a gradient-energy constant independent of the
finite spectral set. No H1 assumption about the infinite solution is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Elliptic.Iteration

theorem exists_finite_angular_gradient_energy_bound {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) {a b a' b' : ℝ} (ha : a < a') (hb : b' < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U F : ℝ → AngularL2), Continuous U → Continuous F →
      (∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t))) →
      (∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t))) →
      (∀ i t, modelJacobi v (angularEigenvalue i) (fun s => inner ℝ (angularBasis i) (U s)) t =
        inner ℝ (angularBasis i) (F t)) →
      ∀ s : Finset AngularIndex,
        (∫ x in cylinderAnnulus a' b', ∑ j : Fin 3,
          (fderiv ℝ (cylinderLift (projectedAngular s U)) x (EuclideanSpace.single j 1)) ^ 2) ≤
        C * ((∫ t in Icc a b, ‖U t‖ ^ 2) + ∫ t in Icc a b, ‖F t‖ ^ 2) := by
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hVO := closure_cylinderAnnulus_subset_punctured a b
  have hV := isOpen_cylinderAnnulus a b
  have hW := isOpen_cylinderAnnulus a' b'
  obtain ⟨Cg, hCg, hgradient⟩ := exists_local_uniform_gradient_integral_le
    (Ω := ({0}ᶜ : Set E)) hO hV (isCompact_closure_cylinderAnnulus a b) hVO
    (subset_closure.trans hVO) hW (isCompact_closure_cylinderAnnulus a' b')
    (closure_cylinderAnnulus_subset_wider ha hb) (κ := 1) (A := 1) (by norm_num) (by norm_num)
  obtain ⟨Cf, hCf, hforcing⟩ := exists_finite_principalForcing_energy_bound hv a b
  refine ⟨Cg * (Real.exp (-2 * a) + Cf), mul_nonneg hCg (by positivity), ?_⟩
  intro U F hU hF hcu hcf heq s
  let u := cylinderLift (projectedAngular s U)
  let f := physicalPrincipalForcing v u (projectedAngular s F)
  have hu : MemLp u 2 (volume.restrict (cylinderShell a b)) :=
    memLp_projectedAngular_lift s hU hcu a b
  obtain ⟨hf, hfbound⟩ := hforcing s U F hU hF hcu hcf
  have hre : volume.restrict (cylinderAnnulus a b) ≤ volume.restrict (cylinderShell a b) :=
    Measure.restrict_mono (cylinderAnnulus_subset_shell a b) le_rfl
  have hus : ContDiffOn ℝ ∞ u ({0}ᶜ : Set E) := by
    intro x hx
    exact (contDiffAt_cylinderLift (smooth_projectedAngular s hcu) (by simpa using hx)).contDiffWithinAt
  have hwe : WeakEquation (cylinderAnnulus a b)
      (matrixFlux (euclideanPrincipalForm ({0}ᶜ : Set E)).a (fun j => partialDeriv j u)) f := by
    have h := weakEquation_finite_native_angular hV (isCompact_closure_cylinderAnnulus a b) hVO
      v s (fun i t => inner ℝ (angularBasis i) (U t))
      (fun i t => inner ℝ (angularBasis i) (F t)) (fun i _ => hcu i) (fun i _ t => heq i t)
    simpa only [finitePhysical_eq_lift, projectedAngular, u, f] using h
  have hg := hgradient (euclideanPrincipalForm ({0}ᶜ : Set E)) (by rfl)
    (fun x _ i j => euclideanPrincipalForm_entry_bound _ x i j)
    hus (hu.mono_measure hre) (hf.mono_measure hre) hwe
  have hubound : (∫ x in cylinderAnnulus a b, u x ^ 2) ≤
      Real.exp (-2 * a) * (∫ t in Icc a b, ‖U t‖ ^ 2) := by
    apply (setIntegral_mono_set hu.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun x => @cylinderAnnulus_subset_shell a b x)).trans
    exact integral_projectedAngular_lift_sq_le s hU hcu a b
  have hfbound' : (∫ x in cylinderAnnulus a b, f x ^ 2) ≤
      Cf * ((∫ t in Icc a b, ‖U t‖ ^ 2) + ∫ t in Icc a b, ‖F t‖ ^ 2) := by
    exact (setIntegral_mono_set hf.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun x => @cylinderAnnulus_subset_shell a b x)).trans hfbound
  apply hg.trans
  have hIF : 0 ≤ ∫ t in Icc a b, ‖F t‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ Cg * (Real.exp (-2 * a) * (∫ t in Icc a b, ‖U t‖ ^ 2) +
        Cf * ((∫ t in Icc a b, ‖U t‖ ^ 2) + ∫ t in Icc a b, ‖F t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hubound hfbound') hCg
    _ ≤ _ := by nlinarith [mul_nonneg hCg (mul_nonneg (Real.exp_pos (-2 * a)).le hIF)]

#print axioms exists_finite_angular_gradient_energy_bound

end Yamabe3.Analysis.SpherePolar
