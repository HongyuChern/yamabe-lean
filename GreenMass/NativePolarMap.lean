import GreenMass.NativeSphereGeometry
import GreenMass.PolarGramJacobian
import PoincareLib.Geometry.Riemannian.Measure.Coarea.Fubini
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual polar coordinates over a native sphere chart

The map and differential below are ordinary maps of Euclidean three-space.
The Jacobian is computed from the native induced sphere metric, rather than
postulated as the definition of an area element.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Poincare.EuclideanSpace
open scoped Manifold ContDiff Bundle Pointwise

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace GreenMass.NativePolarMap

open NativeSphereGeometry

def polarMap (e : V → S) (x : E) : E :=
  x 0 • ((e (euclideanTail x) : S) : E)

def polarDerivative (e : V → S) (x : E) : E →L[ℝ] E :=
  x 0 • ((fderiv ℝ ((Subtype.val : S → E) ∘ e) (euclideanTail x)).comp
    (euclideanTailProjectionCLM 2)) +
      (EuclideanSpace.proj 0).smulRight ((e (euclideanTail x) : S) : E)

theorem hasFDerivAt_polarMap {e : V → S} {x : E}
    (he : MDifferentiableAt (𝓡 2) (𝓡 2) e (euclideanTail x)) :
    HasFDerivAt (polarMap e) (polarDerivative e x) x := by
  have hf : DifferentiableAt ℝ ((Subtype.val : S → E) ∘ e) (euclideanTail x) := by
    exact ((smooth_inclusion.mdifferentiable (by simp) _).comp _ he).differentiableAt
  exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt.smul
    (hf.hasFDerivAt.comp x (euclideanTailProjectionCLM 2).hasFDerivAt)

theorem inner_sphereChart_derivative {e : V → S} {z : V}
    (he : MDifferentiableAt (𝓡 2) (𝓡 2) e z) (v : V) :
    inner ℝ ((e z : S) : E) (fderiv ℝ ((Subtype.val : S → E) ∘ e) z v) = 0 := by
  let f : V → E := (Subtype.val : S → E) ∘ e
  have hf : DifferentiableAt ℝ f z :=
    ((smooth_inclusion.mdifferentiable (by simp) _).comp _ he).differentiableAt
  have hone : (fun w : V => inner ℝ (f w) (f w)) = fun _ => (1 : ℝ) := by
    funext w
    dsimp [f]
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow]
  have h := fderiv_inner_apply ℝ hf hf v
  rw [hone, fderiv_const_apply, zero_apply] at h
  rw [real_inner_comm (f z) (fderiv ℝ f z v)] at h
  change inner ℝ (f z) (fderiv ℝ f z v) = 0
  linarith

theorem polarDerivative_zero (e : V → S) (x : E) :
    polarDerivative e x (EuclideanSpace.basisFun (Fin 3) ℝ 0) =
      ((e (euclideanTail x) : S) : E) := by
  have ht : euclideanTail (EuclideanSpace.basisFun (Fin 3) ℝ 0) = (0 : V) := by
    ext i
    simp [euclideanTail, EuclideanSpace.basisFun_apply]
  simp only [polarDerivative, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, euclideanTailProjectionCLM_apply,
    ContinuousLinearMap.smulRight_apply, ht, map_zero, smul_zero, zero_add]
  simp [EuclideanSpace.basisFun_apply]

theorem polarDerivative_succ (e : V → S) (x : E) (i : Fin 2) :
    polarDerivative e x (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) =
      x 0 • fderiv ℝ ((Subtype.val : S → E) ∘ e) (euclideanTail x)
        (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  have ht : euclideanTail (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) =
      EuclideanSpace.basisFun (Fin 2) ℝ i := by
    ext j
    simp [euclideanTail, EuclideanSpace.basisFun_apply]
  simp only [polarDerivative, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, euclideanTailProjectionCLM_apply,
    ContinuousLinearMap.smulRight_apply, ht]
  simp [EuclideanSpace.basisFun_apply]

/-- The actual polar determinant is the native sphere density multiplied by
the square of the radial coordinate. -/
theorem polarDerivative_abs_det {e : V → S} {x : E}
    (he : MDifferentiableAt (𝓡 2) (𝓡 2) e (euclideanTail x)) :
    |(polarDerivative e x).det| =
      (x 0) ^ 2 * sphereMetric.pullbackVolumeDensity e (euclideanTail x) := by
  rw [sphereMetric_density he]
  exact PolarGramJacobian.abs_det_polar_columns (polarDerivative e x)
    (fderiv ℝ ((Subtype.val : S → E) ∘ e) (euclideanTail x))
    ((e (euclideanTail x) : S) : E) (x 0)
    (norm_eq_of_mem_sphere _) (inner_sphereChart_derivative he)
    (polarDerivative_zero _ _) (polarDerivative_succ _ _)

def polarDomain (s : Set V) : Set E :=
  {x | x 0 ∈ Ioo (0 : ℝ) 1 ∧ euclideanTail x ∈ s}

theorem measurableSet_polarDomain {s : Set V} (hs : MeasurableSet s) :
    MeasurableSet (polarDomain s) :=
  (measurableSet_Ioo.preimage (EuclideanSpace.proj 0).continuous.measurable).inter
    (hs.preimage (continuous_euclideanTail 2).measurable)

theorem polarMap_norm (e : V → S) {x : E} (hx : 0 ≤ x 0) :
    ‖polarMap e x‖ = x 0 := by
  rw [polarMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx,
    norm_eq_of_mem_sphere, mul_one]

theorem polarMap_injOn (e : OpenPartialHomeomorph V S) {s : Set V}
    (hse : s ⊆ e.source) : Set.InjOn (polarMap e) (polarDomain s) := by
  intro x hx y hy hxy
  have hr : x 0 = y 0 := by
    simpa only [polarMap_norm e hx.1.1.le, polarMap_norm e hy.1.1.le] using
      congrArg norm hxy
  have hval : ((e (euclideanTail x) : S) : E) = ((e (euclideanTail y) : S) : E) := by
    apply smul_right_injective E (ne_of_gt hx.1.1)
    simpa only [polarMap, ← hr] using hxy
  have ht : euclideanTail x = euclideanTail y :=
    e.injOn (hse hx.2) (hse hy.2) (Subtype.ext hval)
  calc
    x = euclideanCons (x 0) (euclideanTail x) := (euclideanCons_tail x).symm
    _ = euclideanCons (y 0) (euclideanTail y) := by rw [hr, ht]
    _ = y := euclideanCons_tail y

/-- The image is the actual open Euclidean cone used in `volume.toSphere`. -/
theorem polarMap_image (e : V → S) (s : Set V) :
    polarMap e '' polarDomain s =
      Ioo (0 : ℝ) 1 • ((Subtype.val : S → E) '' (e '' s)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x 0, hx.1, ((e (euclideanTail x) : S) : E),
      ⟨e (euclideanTail x), ⟨euclideanTail x, hx.2, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨r, hr, _, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    refine ⟨euclideanCons r z, ?_, by simp [polarMap]⟩
    simpa only [polarDomain, mem_ofPred_eq, euclideanCons_zero, euclideanTail_cons] using
      And.intro hr hz

#print axioms hasFDerivAt_polarMap
#print axioms polarDerivative_abs_det
#print axioms polarMap_injOn
#print axioms polarMap_image

end GreenMass.NativePolarMap
