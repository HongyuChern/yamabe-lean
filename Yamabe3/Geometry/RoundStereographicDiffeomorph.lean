import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The literal stereographic diffeomorphism of the unit sphere

The chart centered at `q` omits the antipode `-q`.  Its inverse is defined on
all of Euclidean space.  No metric or curvature assumption is an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Yamabe3.Geometry

abbrev RoundStereographicSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

theorem roundStereographic_chart_source {n : ℕ} (q : RoundStereographicSphere n) :
    (chartAt (EuclideanSpace ℝ (Fin n)) q).source = {-q}ᶜ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  change (stereographic' n (-q)).source = {-q}ᶜ
  exact stereographic'_source (-q)

theorem roundStereographic_chart_target {n : ℕ} (q : RoundStereographicSphere n) :
    (chartAt (EuclideanSpace ℝ (Fin n)) q).target = univ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  change (stereographic' n (-q)).target = univ
  exact stereographic'_target (-q)

theorem roundStereographic_chart_center {n : ℕ} (q : RoundStereographicSphere n) :
    chartAt (EuclideanSpace ℝ (Fin n)) q q = 0 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  change (stereographic' n (-q)) q = 0
  simp only [stereographic', OpenPartialHomeomorph.trans_apply]
  rw [stereographic_neg_apply]
  simp

theorem roundStereographic_chart_symm_zero {n : ℕ} (q : RoundStereographicSphere n) :
    (chartAt (EuclideanSpace ℝ (Fin n)) q).symm 0 = q := by
  rw [← roundStereographic_chart_center q]
  exact (chartAt (EuclideanSpace ℝ (Fin n)) q).left_inv (mem_chart_source _ _)

def roundStereographicOpen {n : ℕ} (q : RoundStereographicSphere n) :
    Opens (RoundStereographicSphere n) :=
  ⟨(chartAt (EuclideanSpace ℝ (Fin n)) q).source,
    (chartAt (EuclideanSpace ℝ (Fin n)) q).open_source⟩

@[simp] theorem mem_roundStereographicOpen {n : ℕ}
    (q z : RoundStereographicSphere n) :
    z ∈ roundStereographicOpen q ↔ z ≠ -q := by
  change z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source ↔ _
  rw [roundStereographic_chart_source]
  simp

@[simp] theorem mem_roundStereographicOpen_neg {n : ℕ}
    (p z : RoundStereographicSphere n) :
    z ∈ roundStereographicOpen (-p) ↔ z ≠ p := by
  simp

theorem roundStereographic_chart_symm_contMDiff {n : ℕ}
    (q : RoundStereographicSphere n) :
    ContMDiff (𝓡 n) (𝓡 n) ∞
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm := by
  have h := contMDiffOn_chart_symm (I := 𝓡 n) (x := q) (n := (∞ : ℕ∞ω))
  rw [roundStereographic_chart_target q] at h
  exact contMDiffOn_univ.mp h

/-- The actual chart, restricted to the sphere minus its antipode, as a native
smooth diffeomorphism onto all Euclidean space. -/
def roundStereographicDiffeomorph {n : ℕ} (q : RoundStereographicSphere n) :
    Diffeomorph (𝓡 n) (𝓡 n) (roundStereographicOpen q)
      (EuclideanSpace ℝ (Fin n)) ∞ := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) q
  have ht (x : EuclideanSpace ℝ (Fin n)) : x ∈ c.target := by
    rw [roundStereographic_chart_target]
    exact mem_univ x
  let e : roundStereographicOpen q ≃ EuclideanSpace ℝ (Fin n) := {
    toFun := fun x => c x.val
    invFun := fun y => ⟨c.symm y, c.map_target (ht y)⟩
    left_inv := fun x => Subtype.ext (c.left_inv x.property)
    right_inv := fun y => c.right_inv (ht y) }
  refine { e with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    change ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun z : roundStereographicOpen q => c z.val) x
    apply contMDiffAt_subtype_iff.mpr
    exact (contMDiffOn_chart (I := 𝓡 n) (x := q)).contMDiffAt
      (c.open_source.mem_nhds x.property)
  · apply (ContMDiff.subtypeVal_comp_iff (roundStereographicOpen q) e.symm).mp
    exact roundStereographic_chart_symm_contMDiff q

@[simp] theorem roundStereographicDiffeomorph_apply {n : ℕ}
    (q : RoundStereographicSphere n) (x : roundStereographicOpen q) :
    roundStereographicDiffeomorph q x =
      chartAt (EuclideanSpace ℝ (Fin n)) q x.val := rfl

@[simp] theorem roundStereographicDiffeomorph_symm_coe {n : ℕ}
    (q : RoundStereographicSphere n) (x : EuclideanSpace ℝ (Fin n)) :
    ((roundStereographicDiffeomorph q).symm x : RoundStereographicSphere n) =
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x := rfl

#print axioms roundStereographicDiffeomorph

end Yamabe3.Geometry
