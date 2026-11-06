import Yamabe3.Geometry.RoundStereographicDiffeomorph
import Yamabe3.Geometry.RoundStereographicFactor
import Yamabe3.Geometry.OpenRestriction
import PoincareLib.Topology.Manifold.Surgery.Event.Stereographic.StereographicMetric
import PoincareLib.Geometry.Riemannian.ScalarOperators.Euclidean

/-!
# Actual stereographic metric bridge for the independent W6 branch

The metric is the induced metric of the literal unit sphere.  The chart is
Mathlib's actual stereographic chart, with its radius-two convention.  The
conformal identities below are proved from their differentials.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set PoincareMT PoincareMT.M38
open scoped Manifold ContDiff

namespace Yamabe3.W6

open Yamabe3.Geometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem roundStereographic_inverse_derivative_coe
    (q : RoundStereographicSphere 3) (z : E3) (v : E3) :
    mfderiv (𝓡 3) (𝓡 3)
      (Subtype.val : roundStereographicOpen q → RoundStereographicSphere 3)
      ((roundStereographicDiffeomorph q).symm z)
      (mfderiv (𝓡 3) (𝓡 3) (roundStereographicDiffeomorph q).symm z v) =
    mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-q)) z v := by
  have h := mfderiv_comp z
    (((contMDiff_subtype_val (I := 𝓡 3)
      (U := roundStereographicOpen q) (n := ∞))
      ((roundStereographicDiffeomorph q).symm z)).mdifferentiableAt (by simp))
    ((roundStereographicDiffeomorph q).symm.mdifferentiable (by simp) z)
  have he : (Subtype.val : roundStereographicOpen q → RoundStereographicSphere 3) ∘
      (roundStereographicDiffeomorph q).symm = threeSphereStereoInverse (-q) := rfl
  rw [he] at h
  exact congrArg (fun L => L v) h.symm

/-- The inverse chart pulls back the actual sphere metric to the exact
fourth-power Euclidean scaling. -/
theorem roundStereographic_inverse_metric
    (q : RoundStereographicSphere 3) (z v w : E3) :
    (restrictMetric threeSphereMetric (roundStereographicOpen q)).inner
      ((roundStereographicDiffeomorph q).symm z)
      (mfderiv (𝓡 3) (𝓡 3) (roundStereographicDiffeomorph q).symm z v)
      (mfderiv (𝓡 3) (𝓡 3) (roundStereographicDiffeomorph q).symm z w) =
    roundStereographicFactor z ^ 4 *
      (RiemannianMetric.euclideanMetric 3).inner z v w := by
  rw [restrictMetric_inner, roundStereographic_inverse_derivative_coe,
    roundStereographic_inverse_derivative_coe]
  exact (threeSphereStereoMetric_inner (-q) z v w).trans (by
    rw [roundStereographicFactor_pow_four]
    rfl)

section Inverse

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E3 M] [ChartedSpace E3 N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

/-- Derivatives of a genuine diffeomorphism and its genuine inverse cancel. -/
theorem diffeomorph_symm_mfderiv_apply
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (x : M)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) F.symm (F x)
      (mfderiv (𝓡 3) (𝓡 3) F x v) = v := by
  have hc := mfderiv_comp x (F.symm.mdifferentiable (by simp) (F x))
    (F.mdifferentiable (by simp) x)
  have he : F.symm ∘ F = id := funext F.symm_apply_apply
  rw [he, mfderiv_id] at hc
  exact congrArg (fun L => L v) hc.symm

/-- Inverting an actual conformal metric identity gives the reciprocal
factor.  No existence or conformal-mapping hypothesis is hidden here. -/
theorem conformal_inverse_metric
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (θ : N → ℝ)
    (hθ : ∀ y, θ y ≠ 0)
    (hF : ∀ y v w, g.inner (F.symm y)
      (mfderiv (𝓡 3) (𝓡 3) F.symm y v)
      (mfderiv (𝓡 3) (𝓡 3) F.symm y w) = θ y ^ 4 * h.inner y v w)
    (x : M) (v w : TangentSpace (𝓡 3) x) :
    h.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
      (mfderiv (𝓡 3) (𝓡 3) F x w) =
    (θ (F x))⁻¹ ^ 4 * g.inner x v w := by
  have hm := hF (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
    (mfderiv (𝓡 3) (𝓡 3) F x w)
  rw [diffeomorph_symm_mfderiv_apply, diffeomorph_symm_mfderiv_apply,
    F.symm_apply_apply] at hm
  rw [hm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (hθ (F x))]
  simp

end Inverse

theorem roundStereographic_forward_metric
    (q : RoundStereographicSphere 3) (x : roundStereographicOpen q)
    (v w : TangentSpace (𝓡 3) x) :
    (RiemannianMetric.euclideanMetric 3).inner
      (roundStereographicDiffeomorph q x)
      (mfderiv (𝓡 3) (𝓡 3) (roundStereographicDiffeomorph q) x v)
      (mfderiv (𝓡 3) (𝓡 3) (roundStereographicDiffeomorph q) x w) =
    (roundStereographicFactor (roundStereographicDiffeomorph q x))⁻¹ ^ 4 *
      (restrictMetric threeSphereMetric (roundStereographicOpen q)).inner x v w :=
  conformal_inverse_metric _ _ (roundStereographicDiffeomorph q)
    roundStereographicFactor (fun z => (roundStereographicFactor_pos z).ne')
    (roundStereographic_inverse_metric q) x v w

#print axioms roundStereographic_inverse_metric
#print axioms roundStereographic_forward_metric

end Yamabe3.W6
