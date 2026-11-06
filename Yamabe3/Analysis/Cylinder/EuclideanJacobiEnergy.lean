import Yamabe3.Analysis.Cylinder.NativeSpectralTruncation
import Yamabe3.Analysis.UniformElliptic.LocalCaccioppoli
import Yamabe3.Analysis.UniformElliptic.LocalDivergenceEquation

/-!
# Actual Euclidean Jacobi equations supply the coercive principal equation

The principal form is the genuine identity matrix. Its ellipticity and
entry bounds are proved. The native Euclidean Laplacian is identified
with that form's actual negative-divergence source, so every finite native
angular solution supplies the weak equation needed by Caccioppoli.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

/-- The actual Euclidean identity principal form, with proved ellipticity. -/
def euclideanPrincipalForm (Ω : Set E) : SmoothEllipticBilinearForm 3 Ω where
  a := fun _ => 1
  c := fun _ => 0
  symm := by intros; simp only [Matrix.one_apply, eq_comm]
  smooth_a := by intros; exact contDiff_const
  smooth_c := contDiff_const
  lam := 1
  capLam := 1
  hlam_pos := by norm_num
  hlam_le_capLam := le_rfl
  coercive := by
    intro x hx ξ
    simp only [Poincare.Analysis.Sobolev.Weak.matMulE, Matrix.one_mulVec,
      WithLp.toLp_ofLp, one_mul, real_inner_self_eq_norm_sq, le_refl]

theorem euclideanPrincipalForm_entry_bound (Ω : Set E) (x : E) (i j : Fin 3) :
    |(euclideanPrincipalForm Ω).a x i j| ≤ 1 := by
  change |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem euclidean_laplacian_eq_partial_trace {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) :
    euclideanD.laplacian u x = ∑ i : Fin 3, partialDeriv i (partialDeriv i u) x := by
  rw [euclideanD.laplacian_euclideanMetric hu]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  simp only [EuclideanSpace.basisFun_apply]
  change (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem principalSource_identity_eq_native_negative_laplacian {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) :
    principalSource (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ)) u x =
      -euclideanD.laplacian u x := by
  rw [euclidean_laplacian_eq_partial_trace hu]
  have hflux : matrixFlux (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (fun j => partialDeriv j u) = fun i => partialDeriv i u := by
    funext i y
    simp [matrixFlux, Matrix.one_apply]
  simp only [principalSource, hflux]

def physicalPrincipalForcing (v : ℝ → ℝ) (u : E → ℝ) (f : ℝ × S → ℝ) (x : E) : ℝ :=
  physicalForcing f x / 8 + (15 / 4) * cylinderLift (radialCylinder v) x ^ 4 * u x

theorem weakEquation_of_native_physicalJacobi {O V : Set E}
    (hO : IsOpen O) (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (v : ℝ → ℝ) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u O) (f : ℝ × S → ℝ)
    (heq : ∀ x ∈ O, physicalJacobi v u x = physicalForcing f x) :
    WeakEquation V
      (matrixFlux (euclideanPrincipalForm O).a (fun j => partialDeriv j u))
      (physicalPrincipalForcing v u f) := by
  apply weakEquation_of_local_principalSource (a := fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ))
    hO hV hVc hVO
    (fun _ _ => contDiff_const) hu
  intro x hx
  change principalSource (fun _ : E => (1 : Matrix (Fin 3) (Fin 3) ℝ)) u x = _
  rw [principalSource_identity_eq_native_negative_laplacian
    (hu.contDiffAt (hO.mem_nhds (hVO (subset_closure hx))))]
  have h := heq x (hVO (subset_closure hx))
  unfold physicalJacobi at h
  rw [euclidean_scalarCurvature_zero, zero_mul, add_zero] at h
  unfold physicalPrincipalForcing
  linarith

/-- Every actual finite angular truncation satisfies the true principal
weak equation on each precompact open annulus, with no assumed weak PDE. -/
theorem weakEquation_finite_native_angular {V : Set E}
    (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVzero : closure V ⊆ ({0}ᶜ : Set E)) (v : ℝ → ℝ)
    (s : Finset AngularIndex) (q f : AngularIndex → ℝ → ℝ)
    (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i))
    (heq : ∀ i ∈ s, ∀ t, modelJacobi v (angularEigenvalue i) (q i) t = f i t) :
    WeakEquation V
      (matrixFlux (euclideanPrincipalForm ({0}ᶜ : Set E)).a
        (fun j => partialDeriv j (finitePhysical s q)))
      (physicalPrincipalForcing v (finitePhysical s q) (finiteAngular s f)) := by
  have hu : ContDiffOn ℝ ∞ (finitePhysical s q) ({0}ᶜ : Set E) := by
    intro x hx
    exact (contDiffAt_finitePhysical s q hq (by simpa using hx)).contDiffWithinAt
  exact weakEquation_of_native_physicalJacobi isClosed_singleton.isOpen_compl
    hV hVc hVzero v hu _ (fun x hx =>
      (physicalJacobi_finitePhysical_punctured v s q f hq heq (by simpa using hx)).2)

#print axioms euclideanPrincipalForm
#print axioms principalSource_identity_eq_native_negative_laplacian
#print axioms weakEquation_finite_native_angular

end Yamabe3.Analysis.SpherePolar
