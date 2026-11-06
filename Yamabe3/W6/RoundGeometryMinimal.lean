/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Topology/Manifold/Surgery/Event/Three/ThreeSphereCurvature.lean

Extracts four curvature lemmas with their proofs, makes them private under new names and
computes scalar curvature by tracing the round curvature tensor.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.W6.RoundSphere
import PoincareLib.Topology.Manifold.Surgery.Event.Stereographic.StereographicCurvature
import PoincareLib.Geometry.Riemannian.Curvature.Pullback
import Yamabe3.Geometry.OpenOperators
import Yamabe3.Target.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.NormNum

/-!
# Actual unit-sphere curvature with only its geometric producers

The four private source lemmas are proof-preserving copies of the first four
lemmas of the pinned ThreeSphereCurvature module (revision
62db01af9388dc1d9b56b66d6674f4c09b2318a2). Their statements and proofs are
retained with private names; the unused soliton consequence is not imported.
Scalar curvature is computed directly by tracing the actual curvature tensor
in the metric's own orthonormal basis. No curvature assumption is introduced.

This isolated namespace permits independent compilation before replacing any
existing public RoundGeometry import. Extraction snapshots and byte checks are
kept in sphere_math/evidence/RoundGeometryMinimal_extraction/.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter PoincareMT PoincareMT.M38
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace Yamabe3.W6.MinimalRoundGeometry

abbrev roundMetric : RiemannianMetric 3 Sphere := threeSphereMetric

/-- The center of an inverse stereographic chart is opposite its pole. -/
private theorem source_threeSphereStereoInverse_zero (a : UnitThreeSphere) :
    threeSphereStereoInverse a 0 = -a := by
  apply Subtype.ext
  rw [threeSphereStereoInverse_coe]
  simp [stereoInvFunAux_apply]

/-- The actual inverse chart has invertible differential at every point. -/
private theorem source_threeSphereStereo_invertible (a : UnitThreeSphere)
    (z : EuclideanSpace ℝ (Fin 3)) :
    (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse a) z).IsInvertible := by
  change ((threeSphereStereoLocalDiffeomorph a).mfderivToContinuousLinearEquiv
    (by simp) z).toContinuousLinearMap.IsInvertible
  exact ContinuousLinearMap.isInvertible_equiv

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The center curvature formula transfers through any actual local
isometry from this stereographic metric. -/
private theorem source_curvatureTensor_of_stereoIsometry (a : UnitThreeSphere)
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin 3) → M}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f 0)
    (hinv : ∀ᶠ z in 𝓝 0, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible)
    (hmetric : ∀ᶠ z in 𝓝 0, ∀ u v : EuclideanSpace ℝ (Fin 3),
      (threeSphereStereoMetric a).inner z u v =
        g.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v))
    (u v w z : EuclideanSpace ℝ (Fin 3)) :
    D.curvatureTensor (f 0) (mfderiv (𝓡 3) (𝓡 3) f 0 u)
      (mfderiv (𝓡 3) (𝓡 3) f 0 v) (mfderiv (𝓡 3) (𝓡 3) f 0 w)
      (mfderiv (𝓡 3) (𝓡 3) f 0 z) =
        inner ℝ v z * inner ℝ u w - inner ℝ u z * inner ℝ v w := by
  let DE := (threeSphereStereoMetric a).euclideanLeviCivitaData
  rw [← DE.curvatureTensor_eq_pullback_euclidean D hf hinv hmetric,
    LeviCivitaData.curvatureTensor, threeSphereStereo_curvature_zero,
    threeSphereStereoMetric_inner]
  norm_num [inner_sub_left, real_inner_smul_left]

/-- An orthonormal pair at the image of the chart center has sectional
curvature one. Invertibility supplies its actual coordinate lifts. -/
private theorem source_sectional_one_of_stereoIsometry (a : UnitThreeSphere)
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin 3) → M}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f 0)
    (hinv : ∀ᶠ z in 𝓝 0, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible)
    (hmetric : ∀ᶠ z in 𝓝 0, ∀ u v : EuclideanSpace ℝ (Fin 3),
      (threeSphereStereoMetric a).inner z u v =
        g.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v))
    (u v : TangentSpace (𝓡 3) (f 0))
    (hu : g.inner (f 0) u u = 1) (hv : g.inner (f 0) v v = 1)
    (huv : g.inner (f 0) u v = 0) : D.sectionalCurvature (f 0) u v = 1 := by
  obtain ⟨e, he⟩ := hinv.self_of_nhds
  let u₀ := e.symm u
  let v₀ := e.symm v
  have heu : mfderiv (𝓡 3) (𝓡 3) f 0 u₀ = u := by
    rw [← he]
    exact e.apply_symm_apply u
  have hev : mfderiv (𝓡 3) (𝓡 3) f 0 v₀ = v := by
    rw [← he]
    exact e.apply_symm_apply v
  have hm (b c : EuclideanSpace ℝ (Fin 3)) :
      inner ℝ b c = g.inner (f 0)
        (mfderiv (𝓡 3) (𝓡 3) f 0 b) (mfderiv (𝓡 3) (𝓡 3) f 0 c) := by
    have h := hmetric.self_of_nhds b c
    norm_num [threeSphereStereoMetric_inner] at h
    exact h
  have hc := source_curvatureTensor_of_stereoIsometry a D hf hinv hmetric u₀ v₀ u₀ v₀
  rw [heu, hev, hm, hm, hm, hm, heu, hev, hu, hv, huv, g.symm (f 0) v u, huv]
    at hc
  rw [LeviCivitaData.sectionalCurvature, hc, hu, hv, huv]
  norm_num

/-- The full repeated-pair tensor value is transported through the same
actual isometry; no independence or orthogonality premise is needed. -/
private theorem tensor_pair_of_stereoIsometry (a : UnitThreeSphere)
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin 3) → M}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f 0)
    (hinv : ∀ᶠ z in 𝓝 0, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible)
    (hmetric : ∀ᶠ z in 𝓝 0, ∀ u v : EuclideanSpace ℝ (Fin 3),
      (threeSphereStereoMetric a).inner z u v =
        g.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v))
    (u v : TangentSpace (𝓡 3) (f 0)) :
    D.curvatureTensor (f 0) u v u v =
      g.inner (f 0) v v * g.inner (f 0) u u -
        g.inner (f 0) u v * g.inner (f 0) v u := by
  obtain ⟨e, he⟩ := hinv.self_of_nhds
  let u₀ := e.symm u
  let v₀ := e.symm v
  have heu : mfderiv (𝓡 3) (𝓡 3) f 0 u₀ = u := by
    rw [← he]
    exact e.apply_symm_apply u
  have hev : mfderiv (𝓡 3) (𝓡 3) f 0 v₀ = v := by
    rw [← he]
    exact e.apply_symm_apply v
  have hm (b c : EuclideanSpace ℝ (Fin 3)) :
      inner ℝ b c = g.inner (f 0)
        (mfderiv (𝓡 3) (𝓡 3) f 0 b) (mfderiv (𝓡 3) (𝓡 3) f 0 c) := by
    have h := hmetric.self_of_nhds b c
    norm_num [threeSphereStereoMetric_inner] at h
    exact h
  have hc := source_curvatureTensor_of_stereoIsometry a D hf hinv hmetric u₀ v₀ u₀ v₀
  rw [heu, hev, hm, hm, hm, hm, heu, hev] at hc
  exact hc

private theorem round_curvatureTensor_pair
    (D : LeviCivitaData roundMetric) (x : Sphere)
    (u v : TangentSpace (𝓡 3) x) :
    D.curvatureTensor x u v u v =
      roundMetric.inner x v v * roundMetric.inner x u u -
        roundMetric.inner x u v * roundMetric.inner x v u := by
  have hcenter : threeSphereStereoInverse (-x) 0 = x := by
    rw [source_threeSphereStereoInverse_zero, neg_neg]
  have hi : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z).IsInvertible :=
    Filter.Eventually.of_forall (source_threeSphereStereo_invertible (-x))
  have hm : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      ∀ a b : EuclideanSpace ℝ (Fin 3),
        (threeSphereStereoMetric (-x)).inner z a b =
          roundMetric.inner (threeSphereStereoInverse (-x) z)
            (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z a)
            (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z b) :=
    Filter.Eventually.of_forall (fun _ _ _ => rfl)
  have hc := tensor_pair_of_stereoIsometry (-x) D
    ((threeSphereStereoLocalDiffeomorph (-x)).contMDiff 0) hi hm
  rw [hcenter] at hc
  exact hc u v

/-- The value is literally one; it is not merely an unspecified positive
constant sectional curvature. -/
theorem round_sectionalCurvature_eq_one
    (D : LeviCivitaData roundMetric) (x : Sphere)
    (u v : TangentSpace (𝓡 3) x)
    (hu : roundMetric.inner x u u = 1)
    (hv : roundMetric.inner x v v = 1)
    (huv : roundMetric.inner x u v = 0) :
    D.sectionalCurvature x u v = 1 := by
  have hcenter : threeSphereStereoInverse (-x) 0 = x := by
    rw [source_threeSphereStereoInverse_zero, neg_neg]
  have hi : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z).IsInvertible :=
    Filter.Eventually.of_forall (source_threeSphereStereo_invertible (-x))
  have hm : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      ∀ a b : EuclideanSpace ℝ (Fin 3),
        (threeSphereStereoMetric (-x)).inner z a b =
          roundMetric.inner (threeSphereStereoInverse (-x) z)
            (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z a)
            (mfderiv (𝓡 3) (𝓡 3) (threeSphereStereoInverse (-x)) z b) :=
    Filter.Eventually.of_forall (fun _ _ _ => rfl)
  have hc := source_sectional_one_of_stereoIsometry (-x) D
    ((threeSphereStereoLocalDiffeomorph (-x)).contMDiff 0) hi hm
  rw [hcenter] at hc
  exact hc u v hu hv huv

/-- Direct native trace: the three diagonal sectional slots vanish and
all six ordered off-diagonal orthonormal pair slots equal one. -/
theorem round_scalarCurvature_eq_six
    (D : LeviCivitaData roundMetric) (x : Sphere) :
    D.scalarCurvature x = 6 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : Sphere → Type _) :=
    ⟨roundMetric.toRiemannianMetric⟩
  let b := roundMetric.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    simp [TangentSpace]
  have hinner (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      roundMetric.inner x (b i) (b j) = if i = j then 1 else 0 := by
    change inner ℝ (b i) (b j) = if i = j then 1 else 0
    exact b.inner_eq_ite i j
  have hterm (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      D.curvatureTensor x (b i) (b j) (b i) (b j) =
        1 - (if i = j then (1 : ℝ) else 0) := by
    rw [round_curvatureTensor_pair]
    simp only [hinner, if_pos rfl, one_mul]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hsum (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        (1 - (if i = j then (1 : ℝ) else 0))) = 2 := by
    rw [Finset.sum_sub_distrib]
    norm_num [hdim]
  change (∑ i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
    ∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
      D.curvatureTensor x (b i) (b j) (b i) (b j)) = 6
  simp_rw [hterm, hsum]
  norm_num [hdim]

/-- Scalar curvature remains six on the actual open complement of every
specified finite set. -/
theorem punctured_round_scalarCurvature_eq_six
    (Λ : Finset Sphere) (x : Target.puncturedOpen Λ) :
    (Geometry.restrictMetric roundMetric (Target.puncturedOpen Λ)).leviCivitaData.scalarCurvature x = 6 := by
  rw [Geometry.scalarCurvature_restrictMetric roundMetric (Target.puncturedOpen Λ)
    roundMetric.leviCivitaData _ x]
  exact round_scalarCurvature_eq_six roundMetric.leviCivitaData x.val

/-- The project's geometrically defined equation agrees with the frozen
displayed equation, with coefficient six on both scalar-curvature terms. -/
theorem punctured_round_equation_iff
    (Λ : Finset Sphere) (u : Target.puncturedOpen Λ → ℝ)
    (x : Target.puncturedOpen Λ) :
    let D := (Geometry.restrictMetric roundMetric (Target.puncturedOpen Λ)).leviCivitaData
    (-8 * D.laplacian u x + D.scalarCurvature x * u x = 6 * u x ^ 5) ↔
      (-8 * D.laplacian u x + 6 * u x = 6 * u x ^ 5) := by
  dsimp only
  rw [punctured_round_scalarCurvature_eq_six Λ x]

#print axioms round_sectionalCurvature_eq_one
#print axioms round_scalarCurvature_eq_six
#print axioms punctured_round_scalarCurvature_eq_six
#print axioms punctured_round_equation_iff

end Yamabe3.W6.MinimalRoundGeometry
