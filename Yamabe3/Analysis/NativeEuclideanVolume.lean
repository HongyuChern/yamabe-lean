import PoincareLib.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareLib.Geometry.Riemannian.ScalarOperators.Euclidean

/-!
# Euclidean native volume from the actual identity chart

The proved native coordinate-measure identity is applied to the genuine
identity chart. Its actual Gram matrix is the identity, hence its density
is one. This yields the original normalized Hausdorff Riemannian volume
equal to Lebesgue measure, without importing unused minimizing-geodesic
constructions. No fixed dependency source is modified.
Actual Lean compilation pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory PoincareMT
open scoped Manifold ContDiff ENNReal

namespace Yamabe3.Analysis

theorem native_euclideanMetric_volumeMeasure (n : ℕ) :
    (RiemannianMetric.euclideanMetric n).volumeMeasure =
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let g := RiemannianMetric.euclideanMetric n
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.refl E
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ id univ
    exact contMDiff_id.contMDiffOn
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ id univ
    exact contMDiff_id.contMDiffOn
  have hρ (x : E) : g.pullbackVolumeDensity e x = 1 := by
    change Real.sqrt (Matrix.of (fun i j : Fin n =>
      g.inner x (mfderiv (𝓡 n) (𝓡 n) id x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) id x (EuclideanSpace.basisFun (Fin n) ℝ j)))).det = 1
    simp only [mfderiv_id]
    change Real.sqrt (Matrix.of (fun i j : Fin n =>
      inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j))).det = 1
    have hB : Matrix.of (fun i j : Fin n =>
        inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) = 1 := by
      ext i j
      simpa only [Matrix.of_apply, Matrix.one_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i j
    rw [hB, Matrix.det_one, Real.sqrt_one]
  have hρone : (fun x : E => ENNReal.ofReal (g.pullbackVolumeDensity e x)) =
      fun _ : E => (1 : ℝ≥0∞) := by
    funext x
    rw [hρ, ENNReal.ofReal_one]
  have h := g.map_restrict_volumeMeasure_symm e he hei
  rw [hρone] at h
  change (g.volumeMeasure.restrict univ).map id =
    (volume.withDensity (fun _ : E => (1 : ℝ≥0∞))).restrict univ at h
  simpa only [Measure.restrict_univ, Measure.map_id, withDensity_const, one_smul] using h

#print axioms native_euclideanMetric_volumeMeasure

end Yamabe3.Analysis
