import Yamabe3.Analysis.Sphere.NativeSphereHeight
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Genuine sphere restriction and Euclidean polar trace

The Hessian of an ambient scalar function restricted to the actual induced
unit sphere is computed from its true second fundamental correction.  A
radial vector and the image of the native orthonormal tangent basis form an
actual ambient orthonormal basis.  Tracing gives the angular part of the
ordinary Euclidean Laplacian, with no polar operator assumed as an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open Poincare.Geometry.Riemannian.SpaceForm
open SphereSpectrum

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev S := UnitSphere 2
abbrev sphereD := (roundSphereMetric 2).leviCivitaData
abbrev euclideanD := (RiemannianMetric.euclideanMetric 3).leviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local instance sphereDimensionRestriction : Fact (Module.finrank ℝ E = 2 + 1) :=
  ⟨by simp [E]⟩

theorem hessian_restriction {f : E → ℝ} (x : S)
    (hf : ContDiffAt ℝ ∞ f (x : E)) (u v : TangentSpace (𝓡 2) x) :
    sphereD.hessian (fun y : S => f y) x u v =
      fderiv ℝ (fderiv ℝ f) (x : E)
        (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) x u)
        (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) x v) -
      (roundSphereMetric 2).inner x u v * fderiv ℝ f (x : E) (x : E) := by
  let ι : S → E := Subtype.val
  obtain ⟨B, _, hB⟩ := RiemannianMetric.Induced.exists_normal_hessian_correction
    euclideanD sphereD (F := ι) contMDiff_coe_sphere x
    (Filter.Eventually.of_forall (fun _ _ _ => rfl)) u v
  have hlinear (a : E) : inner ℝ a B =
      -height a x * (roundSphereMetric 2).inner x u v := by
    have hc : ContDiffAt ℝ ∞ (fun y : E => inner ℝ a y) (x : E) :=
      (innerSL ℝ a).contDiff.contDiffAt
    have h := hB (fun y : E => inner ℝ a y) hc.contMDiffAt
    change sphereD.hessian (height a) x u v = _ at h
    rw [euclidean_hessian_linear, zero_add, euclideanD.inner_gradient] at h
    simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at h
    change sphereD.hessian (height a) x u v = fderiv ℝ (fun y : E => inner ℝ a y) (x : E) B at h
    erw [(innerSL ℝ a).fderiv] at h
    rw [hessian_height] at h
    exact h.symm
  have hvec : (B : E) = -(roundSphereMetric 2).inner x u v • (x : E) := by
    apply ext_inner_left (𝕜 := ℝ) (E := E)
    intro a
    rw [hlinear]
    simp only [real_inner_smul_right, height]
    ring
  have h := hB f hf.contMDiffAt
  change sphereD.hessian (fun y : S => f y) x u v = _ at h
  rw [euclideanD.hessian_euclideanMetric hf, euclideanD.inner_gradient] at h
  simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at h
  change sphereD.hessian (fun y : S => f y) x u v =
    fderiv ℝ (fderiv ℝ f) (x : E) (mfderiv (𝓡 2) (𝓡 3) ι x u)
      (mfderiv (𝓡 2) (𝓡 3) ι x v) + fderiv ℝ f (x : E) B at h
  rw [hvec, map_smul] at h
  simpa only [smul_eq_mul, neg_mul, sub_eq_add_neg] using h

abbrev SphereTangentIndex (x : S) := Fin (Module.finrank ℝ (TangentSpace (𝓡 2) x))

def radialTangentialFrame (x : S) : Option (SphereTangentIndex x) → E
  | none => (x : E)
  | some i => mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) x
      ((roundSphereMetric 2).orthonormalBasis x i)

theorem orthonormal_radialTangentialFrame (x : S) :
    Orthonormal ℝ (radialTangentialFrame x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨(roundSphereMetric 2).toRiemannianMetric⟩
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [radialTangentialFrame, ite_true]
      exact inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x)
    | some j =>
      simpa only [radialTangentialFrame, reduceCtorEq, ite_false] using
        sphere_normal_tangent x ((roundSphereMetric 2).orthonormalBasis x j)
  | some i =>
    cases j with
    | none =>
      simpa only [radialTangentialFrame, reduceCtorEq, ite_false, real_inner_comm] using
        sphere_normal_tangent x ((roundSphereMetric 2).orthonormalBasis x i)
    | some j =>
      simp only [radialTangentialFrame, Option.some.injEq]
      change inner ℝ ((roundSphereMetric 2).orthonormalBasis x i)
        ((roundSphereMetric 2).orthonormalBasis x j) = _
      exact orthonormal_iff_ite.mp ((roundSphereMetric 2).orthonormalBasis x).orthonormal i j

def radialTangentialBasis (x : S) : OrthonormalBasis (Option (SphereTangentIndex x)) ℝ E :=
  let b := basisOfOrthonormalOfCardEqFinrank (orthonormal_radialTangentialFrame x)
    (by simp [E, SphereTangentIndex, TangentSpace])
  b.toOrthonormalBasis (by
    dsimp only [b]
    simpa only [coe_basisOfOrthonormalOfCardEqFinrank] using orthonormal_radialTangentialFrame x)

@[simp] theorem radialTangentialBasis_apply (x : S) (i : Option (SphereTangentIndex x)) :
    radialTangentialBasis x i = radialTangentialFrame x i := by
  simp only [radialTangentialBasis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfOrthonormalOfCardEqFinrank]

theorem laplacian_euclidean_in_orthonormalBasis {f : E → ℝ} {y : E}
    (hf : ContDiffAt ℝ ∞ f y) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    euclideanD.laplacian f y =
      ∑ i, fderiv ℝ (fderiv ℝ f) y (b i) (b i) := by
  have hfm := hf.contMDiffAt
  rw [euclideanD.laplacian_eq_trace_connection_gradient hfm]
  change LinearMap.trace ℝ E
    (show E →ₗ[ℝ] E from (euclideanD.connection (euclideanD.gradient f) y).toLinearMap) = _
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (euclideanD.connection (euclideanD.gradient f) y (b i)) = _
  rw [real_inner_comm (F := E) (euclideanD.connection (euclideanD.gradient f) y (b i)) (b i)]
  exact (euclideanD.hessian_eq_inner_connection_gradient hfm (b i) (b i)).symm.trans
    (euclideanD.hessian_euclideanMetric hf (b i) (b i))

theorem laplacian_euclidean_radialFrame {f : E → ℝ} {y : E}
    (hf : ContDiffAt ℝ ∞ f y) (x : S) :
    euclideanD.laplacian f y =
      fderiv ℝ (fderiv ℝ f) y (x : E) (x : E) +
      ∑ i, fderiv ℝ (fderiv ℝ f) y
        (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) x
          ((roundSphereMetric 2).orthonormalBasis x i))
        (mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S → E) x
          ((roundSphereMetric 2).orthonormalBasis x i)) := by
  rw [laplacian_euclidean_in_orthonormalBasis hf (radialTangentialBasis x), Fintype.sum_option]
  simp only [radialTangentialBasis_apply, radialTangentialFrame]

theorem laplacian_restriction {f : E → ℝ} (x : S)
    (hf : ContDiffAt ℝ ∞ f (x : E)) :
    sphereD.laplacian (fun y : S => f y) x = euclideanD.laplacian f (x : E) -
      fderiv ℝ (fderiv ℝ f) (x : E) (x : E) (x : E) -
      2 * fderiv ℝ f (x : E) (x : E) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨(roundSphereMetric 2).toRiemannianMetric⟩
  have hb (i) : (roundSphereMetric 2).inner x
      ((roundSphereMetric 2).orthonormalBasis x i)
      ((roundSphereMetric 2).orthonormalBasis x i) = 1 := by
    change inner ℝ ((roundSphereMetric 2).orthonormalBasis x i)
      ((roundSphereMetric 2).orthonormalBasis x i) = 1
    exact inner_self_eq_one_of_norm_eq_one
      (((roundSphereMetric 2).orthonormalBasis x).norm_eq_one i)
  rw [LeviCivitaData.laplacian]
  simp only [hessian_restriction x hf, hb, one_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by simp [TangentSpace]
  have hdim' : (Module.finrank ℝ (TangentSpace (𝓡 2) x) : ℝ) = 2 := by exact_mod_cast hdim
  rw [hdim']
  rw [laplacian_euclidean_radialFrame hf x]
  ring

#print axioms hessian_restriction
#print axioms laplacian_restriction

end Yamabe3.Analysis.SpherePolar
