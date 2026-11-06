import Yamabe3.Analysis.BoundaryNormalQuantitative
import Yamabe3.Analysis.BoundaryNormalH4
import PoincareLib.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients

/-! The quantitative algebraic recovery is applied to the actual weak Hessian.
Mixed derivatives are identified a.e. by weak derivative uniqueness. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
open Poincare.Analysis.Sobolev.BoundaryNormal
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- These are the actual chosen weak derivatives of the same function,
identified in the same restricted volume measure. -/
theorem chosen_weak_hessian_commute_ae {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : MemWkp 2 2 u O) (i j : Fin d) :
    chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O =ᵐ[volume.restrict O]
      chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O := by
  have hi := chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i
  have hj := chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j
  have hp (k : Fin d) := (hu.chosenWeakPartial_mem k).memW1p
  have hji := chosenWeakPartial'_isWeakPartial_of_mem (hp i) j
  have hij := chosenWeakPartial'_isWeakPartial_of_mem (hp j) i
  exact HasWeakPartialDeriv.ae_eq hO hij (weakPartial_commute i j hi hj hji)
    ((chosenWeakPartial'_memLp_of_mem (hp j) i).locallyIntegrable (by norm_num))
    ((chosenWeakPartial'_memLp_of_mem (hp i) j).locallyIntegrable (by norm_num))

/-- Recover the missing normal second derivative with explicit coefficient
bounds and no solution-dependent ellipticity or coefficient constant. -/
theorem normal_weak_hessian_eLpNorm_bound
    (B : SmoothEllipticBilinearForm d univ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ x ∈ O, ∀ i j, |B.a x i j| ≤ C)
    (hb : ∀ x ∈ O, ∀ i j,
      |fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single i 1)| ≤ D)
    {u f : E → ℝ} (hu : MemWkp 2 2 u O) (hf : MemLp f 2 (volume.restrict O))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    eLpNorm (chosenWeakPartial' 2 0 (chosenWeakPartial' 2 0 u O) O) 2 (volume.restrict O) ≤
      ENNReal.ofReal B.lam⁻¹ *
        (eLpNorm f 2 (volume.restrict O) + ENNReal.ofReal C *
          (∑ ij ∈ (Finset.univ : Finset (Fin d × Fin d)).erase (0, 0),
            eLpNorm (chosenWeakPartial' 2 ij.1 (chosenWeakPartial' 2 ij.2 u O) O) 2 (volume.restrict O)) +
          ENNReal.ofReal D * ∑ ij : Fin d × Fin d,
            eLpNorm (chosenWeakPartial' 2 ij.2 u O) 2 (volume.restrict O)) := by
  let p (j : Fin d) := chosenWeakPartial' 2 j u O
  let q (i j : Fin d) := chosenWeakPartial' 2 i (p j) O
  have hp (j : Fin d) := (hu.chosenWeakPartial_mem j).memW1p
  have hq (i j : Fin d) := chosenWeakPartial'_memLp_of_mem (hp j) i
  apply normal_component_eLpNorm_bound (volume.restrict O) (0, 0)
    (fun ij : Fin d × Fin d => fun x => B.a x ij.1 ij.2) (fun ij => q ij.1 ij.2)
    (fun ij : Fin d × Fin d => fun x =>
      fderiv ℝ (fun y => B.a y ij.1 ij.2) x (EuclideanSpace.single ij.1 1))
    (fun ij => p ij.2) f B.lam C D B.hlam_pos hC hD
  · exact Eventually.of_forall fun x => by
      have h := B.coercive x (mem_univ x) (EuclideanSpace.single 0 1)
      simpa [matMulE, Matrix.mulVec, dotProduct, EuclideanSpace.inner_single_left] using h
  · filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact fun ij _ => ha x hx ij.1 ij.2
  · filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact fun ij => hb x hx ij.1 ij.2
  · filter_upwards [weak_hessian_equation_ae hO hOc B.a B.smooth_a hu hf heq] with x hx
    simpa only [Fintype.sum_prod_type, Finset.sum_add_distrib, p, q] using hx
  · exact hf.aestronglyMeasurable
  · exact fun ij => (hq ij.1 ij.2).aestronglyMeasurable
  · exact fun ij => (hp ij.2).1.aestronglyMeasurable

#print axioms chosen_weak_hessian_commute_ae
#print axioms normal_weak_hessian_eLpNorm_bound
end Yamabe3.Analysis.UniformElliptic
