import Yamabe3.Analysis.Cylinder.NativeFiniteGradientEnergy
import Yamabe3.Analysis.UniformElliptic.SmoothApproximationH1
import PoincareLib.Analysis.Parabolic.Dirichlet.SpectralCompactness

/-!
# Actual H1 regularity of the same reconstructed angular solution

The actual compact sphere resolvent proves countability of its eigenbasis.
One genuine finite exhaustion gives smooth physical approximants with the
proved native equations, true local L2 convergence, and a common actual
Caccioppoli energy bound. Hahn--Banach/Riesz therefore constructs L2 weak
first derivatives of the very same lifted joint representative.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.UniformElliptic
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Geometry.Riemannian.SpaceForm
open Poincare.Analysis.Sobolev.Weak

theorem countable_angularIndex : Countable AngularIndex :=
  Poincare.Analysis.Dirichlet.CompactSpectral.countable_basisIndex
    (domainL2Resolvent (roundSphereMetric 2).leviCivitaData univ)
    (isCompactOperator_domainL2Resolvent (roundSphereMetric 2).leviCivitaData univ
      (by decide) isOpen_univ (by simpa using (isCompact_univ : IsCompact (univ : Set S))))
    domainL2Resolvent_isSelfAdjoint

/-- Actual local H1 on every fixed annulus. All derivatives are constructed
from the same genuine joint representative; no derivative or regularity
certificate of the infinite sum is supplied. -/
theorem native_angular_curve_has_weak_partials_on_annulus
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    {U F : ℝ → AngularL2} (hU : Continuous U) (hF : Continuous F)
    (hcu : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t)))
    (hcf : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t)))
    (heq : ∀ i t, modelJacobi v (angularEigenvalue i) (fun s => inner ℝ (angularBasis i) (U s)) t =
      inner ℝ (angularBasis i) (F t))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ)) (c : ℝ) :
    MemLp (cylinderLift w) 2 (volume.restrict (cylinderAnnulus (c - 1) (c + 1))) ∧
    ∃ p : Fin 3 → Lp ℝ 2 (volume.restrict (cylinderAnnulus (c - 1) (c + 1))),
      ∀ i, HasWeakPartialDeriv i (p i) (cylinderLift w) (cylinderAnnulus (c - 1) (c + 1)) := by
  classical
  let : Countable AngularIndex := countable_angularIndex
  obtain ⟨s, -, hs⟩ := exists_finite_basis_exhaustion (ι := AngularIndex)
  let W := cylinderAnnulus (c - 1) (c + 1)
  let K := cylinderShell (c - 1) (c + 1)
  let uSeq : ℕ → E → ℝ := fun n => cylinderLift (projectedAngular (s n) U)
  have huK : MemLp (cylinderLift w) 2 (volume.restrict K) :=
    memLp_cylinderLift_on_shell hw _ _ (native_joint_memLp_interval hU hw hae _ _)
  have hWK : W ⊆ K := cylinderAnnulus_subset_shell _ _
  have huW := huK.mono_measure (Measure.restrict_mono hWK le_rfl)
  refine ⟨huW, ?_⟩
  obtain ⟨C, hC, henergy⟩ := exists_finite_angular_gradient_energy_bound hv
    (a := c - 2) (b := c + 2) (a' := c - 1) (b' := c + 1) (by linarith) (by linarith)
  let B := C * ((∫ t in Icc (c - 2) (c + 2), ‖U t‖ ^ 2) +
    ∫ t in Icc (c - 2) (c + 2), ‖F t‖ ^ 2)
  have hB : 0 ≤ B := mul_nonneg hC (add_nonneg
    (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _)))
  have hgrad (n : ℕ) : (∫ x in W, ∑ i : Fin 3,
      (fderiv ℝ (uSeq n) x (EuclideanSpace.single i 1)) ^ 2) ≤ B :=
    henergy U F hU hF hcu hcf heq (s n)
  have hsmooth (n : ℕ) : ContDiffOn ℝ ∞ (uSeq n) ({0}ᶜ : Set E) := by
    intro x hx
    exact (contDiffAt_cylinderLift (smooth_projectedAngular (s n) hcu)
      (by simpa using hx)).contDiffWithinAt
  have hlimK := integral_projectedAngular_lift_error_tendsto hs hU hcu hw hae (c - 1) (c + 1)
  have hlimW : Tendsto (fun n => ∫ x in W, (uSeq n x - cylinderLift w x) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) ?_ hlimK
    intro n
    apply setIntegral_mono_set
      ((memLp_projectedAngular_lift (s n) hU hcu (c - 1) (c + 1)).sub huK).integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _)
    exact Eventually.of_forall fun x => @hWK x
  obtain ⟨p, -, hp⟩ := exists_weak_partials_of_local_smooth_approximation
    isClosed_singleton.isOpen_compl (isOpen_cylinderAnnulus _ _)
    (isCompact_closure_cylinderAnnulus _ _) (closure_cylinderAnnulus_subset_punctured _ _)
    huW uSeq hsmooth hlimW hB hgrad
  exact ⟨p, hp⟩

/-- Every actual nonzero Euclidean point has an open neighborhood where
the same lifted solution has actual L2 weak first derivatives. -/
theorem native_angular_curve_has_local_H1
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    {U F : ℝ → AngularL2} (hU : Continuous U) (hF : Continuous F)
    (hcu : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (U t)))
    (hcf : ∀ i, ContDiff ℝ ∞ (fun t => inner ℝ (angularBasis i) (F t)))
    (heq : ∀ i t, modelJacobi v (angularEigenvalue i) (fun s => inner ℝ (angularBasis i) (U s)) t =
      inner ℝ (angularBasis i) (F t))
    {w : ℝ × S → ℝ} (hw : Measurable w)
    (hae : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume] (U t : S → ℝ))
    {x : E} (hx : x ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ ({0}ᶜ : Set E) ∧
      MemLp (cylinderLift w) 2 (volume.restrict V) ∧
      ∃ p : Fin 3 → Lp ℝ 2 (volume.restrict V),
        ∀ i, HasWeakPartialDeriv i (p i) (cylinderLift w) V := by
  let c := -Real.log ‖x‖
  exact ⟨cylinderAnnulus (c - 1) (c + 1), isOpen_cylinderAnnulus _ _,
    mem_cylinderAnnulus_of_log_norm hx (by dsimp [c]; linarith) (by dsimp [c]; linarith),
    isCompact_closure_cylinderAnnulus _ _, closure_cylinderAnnulus_subset_punctured _ _,
    native_angular_curve_has_weak_partials_on_annulus hv hU hF hcu hcf heq hw hae c⟩

#print axioms countable_angularIndex
#print axioms native_angular_curve_has_local_H1

end Yamabe3.Analysis.SpherePolar
