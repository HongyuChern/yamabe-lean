import PoincareLib.Geometry.Riemannian.SpaceForm.RoundSphere
import PoincareLib.Geometry.Riemannian.Metric.Induced.Hessian
import PoincareLib.Geometry.Riemannian.Connection.Construction

/-!
# Actual height functions on the induced round sphere

The Hessian formula is derived from the actual inclusion and its actual
Levi-Civita connections.  The unit-radius constraint identifies the normal
correction.  In particular no spherical eigenvalue is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local instance sphereDimension (n : ℕ) :
    Fact (Module.finrank ℝ (Ambient n) = n + 1) := ⟨by simp [Ambient]⟩

def height {n : ℕ} (a : Ambient n) (x : UnitSphere n) : ℝ :=
  inner ℝ a (x : Ambient n)

theorem smooth_height {n : ℕ} (a : Ambient n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (height a) := by
  exact (innerSL ℝ a).contDiff.contMDiff.comp contMDiff_coe_sphere

theorem euclidean_hessian_normSq {n : ℕ}
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric n))
    (x u v : EuclideanSpace ℝ (Fin n)) :
    D.hessian (fun y => ‖y‖ ^ 2) x u v = 2 * inner ℝ u v := by
  rw [D.hessian_euclideanMetric (contDiff_norm_sq ℝ).contDiffAt, fderiv_norm_sq,
    two_smul, fderiv_add (innerSL ℝ).differentiableAt (innerSL ℝ).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, add_apply]
  change inner ℝ u v + inner ℝ u v = 2 * inner ℝ u v
  ring

theorem euclidean_hessian_linear {n : ℕ}
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric n))
    (a x u v : EuclideanSpace ℝ (Fin n)) :
    D.hessian (fun y => inner ℝ a y) x u v = 0 := by
  erw [D.hessian_euclideanMetric (innerSL ℝ a).contDiff.contDiffAt]
  have hd : fderiv ℝ ((innerSL ℝ a) : EuclideanSpace ℝ (Fin n) → ℝ) =
      fun _ => innerSL ℝ a := by
    funext y
    exact (innerSL ℝ a).fderiv
  rw [hd]
  simp

theorem sphere_normal_tangent {n : ℕ} (x : UnitSphere n)
    (v : TangentSpace (𝓡 n) x) :
    inner ℝ (x : Ambient n)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (Subtype.val : UnitSphere n → Ambient n) x v) = 0 := by
  have hr : (mfderiv (𝓡 n) (𝓡 (n + 1))
      (Subtype.val : UnitSphere n → Ambient n) x).range =
      (ℝ ∙ (x : Ambient n))ᗮ := by
    convert! range_mvfderiv_subtypeVal x
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← hr]
  exact ⟨v, rfl⟩

theorem normal_vector_eq_radial {n : ℕ} (x : UnitSphere n) (B : Ambient n)
    (hB : ∀ v : TangentSpace (𝓡 n) x, inner ℝ B
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (Subtype.val : UnitSphere n → Ambient n) x v) = 0) :
    B = inner ℝ (x : Ambient n) B • (x : Ambient n) := by
  let Z : Ambient n := B - inner ℝ (x : Ambient n) B • (x : Ambient n)
  have hx : inner ℝ (x : Ambient n) (x : Ambient n) = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x)
  have hZ : inner ℝ (x : Ambient n) Z = 0 := by
    simp [Z, inner_sub_right, inner_smul_right]
  have hr : (mfderiv (𝓡 n) (𝓡 (n + 1))
      (Subtype.val : UnitSphere n → Ambient n) x).range =
      (ℝ ∙ (x : Ambient n))ᗮ := by
    convert! range_mvfderiv_subtypeVal x
  have hmem : Z ∈ (mfderiv (𝓡 n) (𝓡 (n + 1))
      (Subtype.val : UnitSphere n → Ambient n) x).range := by
    rw [hr]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hZ
  obtain ⟨v, hv⟩ := hmem
  have hzB : inner ℝ B Z = 0 := by rw [← hv]; exact hB v
  have hzz : inner ℝ Z Z = 0 := by
    calc
      inner ℝ Z Z = inner ℝ B Z - inner ℝ (x : Ambient n) B *
          inner ℝ (x : Ambient n) Z := by
        conv_lhs => arg 2; unfold Z
        simp only [inner_sub_left, real_inner_smul_left]
      _ = 0 := by rw [hzB, hZ]; ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzz)

theorem hessian_height {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    (a : Ambient n) (x : UnitSphere n) (u v : TangentSpace (𝓡 n) x) :
    D.hessian (height a) x u v =
      -height a x * (roundSphereMetric n).inner x u v := by
  let DA := (RiemannianMetric.euclideanMetric (n + 1)).leviCivitaData
  let F : UnitSphere n → Ambient n := Subtype.val
  obtain ⟨B, hBn, hB⟩ := RiemannianMetric.Induced.exists_normal_hessian_correction
    DA D (F := F) contMDiff_coe_sphere x
    (Filter.Eventually.of_forall (fun _ _ _ => rfl)) u v
  have hrad : B = inner ℝ (x : Ambient n) B • (x : Ambient n) :=
    normal_vector_eq_radial x B hBn
  have hnorm : (fun y : UnitSphere n => ‖(y : Ambient n)‖ ^ 2) = fun _ => 1 := by
    funext y
    rw [norm_eq_of_mem_sphere y, one_pow]
  have hns : ContDiffAt ℝ ∞ (fun y : Ambient n => ‖y‖ ^ 2) (x : Ambient n) :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hn := hB (fun y : Ambient n => ‖y‖ ^ 2) hns.contMDiffAt
  change D.hessian (fun y : UnitSphere n => ‖(y : Ambient n)‖ ^ 2) x u v =
    DA.hessian (fun y : Ambient n => ‖y‖ ^ 2) (x : Ambient n)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) F x u)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) F x v) +
      (RiemannianMetric.euclideanMetric (n + 1)).inner (x : Ambient n)
        (DA.gradient (fun y : Ambient n => ‖y‖ ^ 2) (x : Ambient n)) B at hn
  rw [hnorm, euclidean_hessian_normSq, DA.inner_gradient] at hn
  have hc : D.hessian (fun _ : UnitSphere n => (1 : ℝ)) x u v = 0 := by
    simp [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields, mvfderiv_const]
  rw [hc] at hn
  simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at hn
  change 0 = 2 * inner ℝ
    (mfderiv (𝓡 n) (𝓡 (n + 1)) F x u)
    (mfderiv (𝓡 n) (𝓡 (n + 1)) F x v) +
    fderiv ℝ (fun y : Ambient n => ‖y‖ ^ 2) (x : Ambient n) B at hn
  rw [fderiv_norm_sq_apply] at hn
  simp only [two_smul, add_apply] at hn
  change 0 = 2 * inner ℝ
    (mfderiv (𝓡 n) (𝓡 (n + 1)) F x u)
    (mfderiv (𝓡 n) (𝓡 (n + 1)) F x v) +
    (inner ℝ (x : Ambient n) B + inner ℝ (x : Ambient n) B) at hn
  have hpair : inner ℝ (x : Ambient n) B = -(roundSphereMetric n).inner x u v := by
    change inner ℝ (x : Ambient n) B = -inner ℝ
      (mfderiv (𝓡 n) (𝓡 (n + 1)) F x u)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) F x v)
    linarith
  have hls : ContDiffAt ℝ ∞ (fun y : Ambient n => inner ℝ a y) (x : Ambient n) :=
    (innerSL ℝ a).contDiff.contDiffAt
  have hl := hB (fun y : Ambient n => inner ℝ a y) hls.contMDiffAt
  change D.hessian (height a) x u v = _ at hl
  rw [euclidean_hessian_linear, zero_add, DA.inner_gradient] at hl
  simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at hl
  change D.hessian (height a) x u v =
    fderiv ℝ (fun y : Ambient n => inner ℝ a y) (x : Ambient n) B at hl
  erw [(innerSL ℝ a).fderiv] at hl
  rw [hl, hrad, map_smul, hpair]
  simp only [smul_eq_mul]
  change -(roundSphereMetric n).inner x u v * height a x = _
  ring

theorem laplacian_height {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    (a : Ambient n) (x : UnitSphere n) :
    D.laplacian (height a) x = -(n : ℝ) * height a x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : UnitSphere n → Type _) :=
    ⟨(roundSphereMetric n).toRiemannianMetric⟩
  have hb (i) : (roundSphereMetric n).inner x
      ((roundSphereMetric n).orthonormalBasis x i)
      ((roundSphereMetric n).orthonormalBasis x i) = 1 := by
    change inner ℝ ((roundSphereMetric n).orthonormalBasis x i)
      ((roundSphereMetric n).orthonormalBasis x i) = 1
    exact inner_self_eq_one_of_norm_eq_one
      (((roundSphereMetric n).orthonormalBasis x).norm_eq_one i)
  simp only [LeviCivitaData.laplacian, hessian_height, hb, mul_one]
  simp [TangentSpace]

#print axioms hessian_height
#print axioms laplacian_height

end Yamabe3.Analysis.SphereSpectrum
