import Yamabe3.W6.StereographicBridge
import Yamabe3.W6.EuclideanPuncture
import Yamabe3.Target.Statement
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The exact complement of two prescribed sphere points

Stereographic projection omits the first input point.  A Euclidean translation
sends the second input point to zero.  The resulting map is a constructed
smooth diffeomorphism from the literal two-point complement to punctured R³.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace PoincareMT PoincareMT.M38
open scoped Manifold ContDiff

namespace Yamabe3.W6

open Yamabe3.Geometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => RoundStereographicSphere 3

def twoPointOpen (p q : S3) : Opens S3 := by
  classical
  exact Target.puncturedOpen {p, q}

@[simp] theorem mem_twoPointOpen (p q x : S3) :
    x ∈ twoPointOpen p q ↔ x ≠ p ∧ x ≠ q := by
  classical
  simp [twoPointOpen, Target.puncturedOpen, not_or]

def pointChart (p : S3) : OpenPartialHomeomorph S3 E3 := chartAt E3 (-p)

theorem pointChart_source (p x : S3) : x ∈ (pointChart p).source ↔ x ≠ p := by
  rw [pointChart, roundStereographic_chart_source]
  simp

theorem pointChart_target (p : S3) (z : E3) : z ∈ (pointChart p).target := by
  rw [pointChart, roundStereographic_chart_target]
  exact mem_univ _

theorem pointChart_left_inv (p x : S3) (hx : x ≠ p) :
    (pointChart p).symm (pointChart p x) = x :=
  (pointChart p).left_inv ((pointChart_source p x).mpr hx)

theorem pointChart_right_inv (p : S3) (z : E3) :
    pointChart p ((pointChart p).symm z) = z :=
  (pointChart p).right_inv (pointChart_target p z)

theorem pointChart_symm_ne_pole (p : S3) (z : E3) :
    (pointChart p).symm z ≠ p :=
  (pointChart_source p _).mp ((pointChart p).map_target (pointChart_target p z))

theorem pointChart_contMDiffAt (p x : S3) (hx : x ≠ p) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (pointChart p) x :=
  (contMDiffOn_chart (I := 𝓡 3) (x := -p)).contMDiffAt
    ((pointChart p).open_source.mem_nhds ((pointChart_source p x).mpr hx))

theorem pointChart_symm_contMDiff (p : S3) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (pointChart p).symm :=
  roundStereographic_chart_symm_contMDiff (-p)

def twoPointEquiv (p q : S3) (hpq : p ≠ q) :
    twoPointOpen p q ≃ euclideanPuncturedOpen where
  toFun x := ⟨pointChart p x.val - pointChart p q, by
    rw [mem_euclideanPuncturedOpen]
    intro hz
    have hx := (mem_twoPointOpen p q x.val).mp x.property
    have heq := (pointChart p).injOn ((pointChart_source p x.val).mpr hx.1)
      ((pointChart_source p q).mpr hpq.symm) (sub_eq_zero.mp hz)
    exact hx.2 heq⟩
  invFun y := ⟨(pointChart p).symm (y.val + pointChart p q), by
    rw [mem_twoPointOpen]
    refine ⟨pointChart_symm_ne_pole p _, ?_⟩
    intro heq
    have hc := congrArg (pointChart p) heq
    rw [pointChart_right_inv] at hc
    have hy := (mem_euclideanPuncturedOpen y.val).mp y.property
    exact hy (add_right_cancel (show y.val + pointChart p q =
      0 + pointChart p q by simpa using hc))⟩
  left_inv x := by
    apply Subtype.ext
    change (pointChart p).symm
      (pointChart p x.val - pointChart p q + pointChart p q) = x.val
    rw [sub_add_cancel]
    exact pointChart_left_inv p x.val ((mem_twoPointOpen p q x.val).mp x.property).1
  right_inv y := by
    apply Subtype.ext
    change pointChart p ((pointChart p).symm (y.val + pointChart p q)) -
      pointChart p q = y.val
    rw [pointChart_right_inv, add_sub_cancel_right]

/-- The actual prescribed-point coordinate map, including both inverse
identities and native manifold smoothness. -/
def twoPointDiffeomorph (p q : S3) (hpq : p ≠ q) :
    Diffeomorph (𝓡 3) (𝓡 3) (twoPointOpen p q) euclideanPuncturedOpen ∞ := by
  refine { twoPointEquiv p q hpq with
    contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff euclideanPuncturedOpen
      (twoPointEquiv p q hpq)).mp
    intro x
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun y : twoPointOpen p q => pointChart p y.val - pointChart p q) x
    have hSmooth : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (fun y : S3 => pointChart p y - pointChart p q) x.val :=
      (pointChart_contMDiffAt p x.val
        ((mem_twoPointOpen p q x.val).mp x.property).1).sub contMDiffAt_const
    exact hSmooth.comp x
      (contMDiff_subtype_val (I := 𝓡 3) (U := twoPointOpen p q) (n := ∞) x)
  · apply (ContMDiff.subtypeVal_comp_iff (twoPointOpen p q)
      (twoPointEquiv p q hpq).symm).mp
    exact (pointChart_symm_contMDiff p).comp
      ((contMDiff_subtype_val (I := 𝓡 3) (U := euclideanPuncturedOpen) (n := ∞)).add
        contMDiff_const)

@[simp] theorem twoPointDiffeomorph_coe_apply (p q : S3) (hpq : p ≠ q)
    (x : twoPointOpen p q) :
    (twoPointDiffeomorph p q hpq x : E3) =
      pointChart p x.val - pointChart p q := rfl

@[simp] theorem twoPointDiffeomorph_symm_coe (p q : S3) (hpq : p ≠ q)
    (z : euclideanPuncturedOpen) :
    ((twoPointDiffeomorph p q hpq).symm z : S3) =
      (pointChart p).symm (z.val + pointChart p q) := rfl

theorem translated_inverse_derivative (p q : S3) (z : E3) :
    mfderiv (𝓡 3) (𝓡 3)
      (fun y : E3 => (pointChart p).symm (y + pointChart p q)) z =
    mfderiv (𝓡 3) (𝓡 3) (pointChart p).symm (z + pointChart p q) := by
  have hT : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun y : E3 => y + pointChart p q) := contMDiff_id.add contMDiff_const
  have h := mfderiv_comp z
    ((pointChart_symm_contMDiff p).mdifferentiable (by simp) _)
    (hT.mdifferentiable (by simp) z)
  have hd : mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => y + pointChart p q) z =
      ContinuousLinearMap.id ℝ E3 := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id z).add_const (pointChart p q)).fderiv
  ext v
  have hv := congrArg (fun L => L v) h
  change mfderiv (𝓡 3) (𝓡 3)
      (fun y : E3 => (pointChart p).symm (y + pointChart p q)) z v =
    mfderiv (𝓡 3) (𝓡 3) (pointChart p).symm (z + pointChart p q)
      (mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => y + pointChart p q) z v) at hv
  have hdv : mfderiv (𝓡 3) (𝓡 3) (fun y : E3 => y + pointChart p q) z v = v :=
    congrArg (fun L => L v) hd
  rw [hdv] at hv
  exact hv

theorem twoPoint_inverse_derivative_coe (p q : S3) (hpq : p ≠ q)
    (z : euclideanPuncturedOpen) (v : TangentSpace (𝓡 3) z) :
    mfderiv (𝓡 3) (𝓡 3) (Subtype.val : twoPointOpen p q → S3)
      ((twoPointDiffeomorph p q hpq).symm z)
      (mfderiv (𝓡 3) (𝓡 3) (twoPointDiffeomorph p q hpq).symm z v) =
    mfderiv (𝓡 3) (𝓡 3) (pointChart p).symm (z.val + pointChart p q)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : euclideanPuncturedOpen → E3) z v) := by
  have hleft := mfderiv_comp z
    (((contMDiff_subtype_val (I := 𝓡 3) (U := twoPointOpen p q) (n := ∞))
      ((twoPointDiffeomorph p q hpq).symm z)).mdifferentiableAt (by simp))
    ((twoPointDiffeomorph p q hpq).symm.mdifferentiable (by simp) z)
  have hG : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun y : E3 => (pointChart p).symm (y + pointChart p q)) :=
    (pointChart_symm_contMDiff p).comp (contMDiff_id.add contMDiff_const)
  have hright := mfderiv_comp z (hG.mdifferentiable (by simp) z.val)
    (((contMDiff_subtype_val (I := 𝓡 3) (U := euclideanPuncturedOpen)
      (n := ∞)) z).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) (hleft.symm.trans hright)
  rw [translated_inverse_derivative] at he
  exact he

/-- The metric relation is computed for the same actual coordinate map
that sends the exact two input points to the Euclidean ends. -/
theorem twoPoint_inverse_metric (p q : S3) (hpq : p ≠ q)
    (z : euclideanPuncturedOpen) (v w : TangentSpace (𝓡 3) z) :
    (restrictMetric threeSphereMetric (twoPointOpen p q)).inner
      ((twoPointDiffeomorph p q hpq).symm z)
      (mfderiv (𝓡 3) (𝓡 3) (twoPointDiffeomorph p q hpq).symm z v)
      (mfderiv (𝓡 3) (𝓡 3) (twoPointDiffeomorph p q hpq).symm z w) =
    roundStereographicFactor (z.val + pointChart p q) ^ 4 *
      (restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen).inner
        z v w := by
  simp only [restrictMetric_inner, twoPoint_inverse_derivative_coe,
    roundStereographicFactor_pow_four, RiemannianMetric.euclideanMetric_inner]
  exact threeSphereStereoMetric_inner (-(-p)) (z.val + pointChart p q) _ _

theorem twoPoint_forward_metric (p q : S3) (hpq : p ≠ q)
    (x : twoPointOpen p q) (v w : TangentSpace (𝓡 3) x) :
    (restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen).inner
      (twoPointDiffeomorph p q hpq x)
      (mfderiv (𝓡 3) (𝓡 3) (twoPointDiffeomorph p q hpq) x v)
      (mfderiv (𝓡 3) (𝓡 3) (twoPointDiffeomorph p q hpq) x w) =
    (roundStereographicFactor (pointChart p x.val))⁻¹ ^ 4 *
      (restrictMetric threeSphereMetric (twoPointOpen p q)).inner x v w := by
  have h := conformal_inverse_metric
    (restrictMetric threeSphereMetric (twoPointOpen p q))
    (restrictMetric (RiemannianMetric.euclideanMetric 3) euclideanPuncturedOpen)
    (twoPointDiffeomorph p q hpq)
    (fun z => roundStereographicFactor (z.val + pointChart p q))
    (fun z => (roundStereographicFactor_pos _).ne')
    (twoPoint_inverse_metric p q hpq) x v w
  simpa only [twoPointDiffeomorph_coe_apply, sub_add_cancel] using h

#print axioms twoPointDiffeomorph
#print axioms twoPoint_inverse_metric
#print axioms twoPoint_forward_metric

end Yamabe3.W6
