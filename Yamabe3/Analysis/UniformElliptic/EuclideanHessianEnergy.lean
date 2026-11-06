import PoincareLib.Analysis.Elliptic.Regularity.Iteration.TestCalculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Explicit Euclidean Hessian energy identity

For actual smooth compactly supported functions, two integrations by parts
prove the exact identity ∫(Δu)² = ∫|D²u|². This is the fixed-coefficient anchor
for a uniform perturbative estimate; no coefficient-dependent chosen constant
enters it.

Proof architecture adapted from the fixed PoincareLib module
`Analysis/Parabolic/WeakRegularity/Interior/PrincipalHessianBound.lean` and
its `ConstantEnergy.lean` dependency, itself adapted from AxelWorkspace
revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e (Apache-2.0).
The present proof is spatial Euclidean, uses the existing actual partialDeriv,
and invokes the Mathlib integration-by-parts theorem directly. Upstream files
are unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Squared Hilbert--Schmidt norm of the actual classical Hessian. -/
def hessianSq (u : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, (partialDeriv i (partialDeriv j u) x) ^ 2

/-- The Euclidean Laplacian with sign div grad. -/
def euclideanLaplacian (u : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, partialDeriv i (partialDeriv i u) x

private theorem integral_partial_mul_eq_neg_mul_partial
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (i : Fin d) :
    (∫ x, partialDeriv i f x * g x) = -(∫ x, f x * partialDeriv i g x) := by
  have hleft : Integrable (fun x => partialDeriv i f x * g x) volume :=
    ((contDiff_partial hf i).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_partial hfc i).mul_right
  have hright : Integrable (fun x => f x * partialDeriv i g x) volume :=
    (hf.continuous.mul (contDiff_partial hg i).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_partial hgc i).mul_left
  have hprod : Integrable (fun x => f x * g x) volume :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := EuclideanSpace.single i 1) hleft hright hprod
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)
  change (∫ x, f x * partialDeriv i g x) = -(∫ x, partialDeriv i f x * g x) at h
  linarith

/-- The diagonal cross term is an actual mixed-Hessian square. -/
theorem integral_diagonal_second_mul
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (i j : Fin d) :
    (∫ x, partialDeriv i (partialDeriv i u) x * partialDeriv j (partialDeriv j u) x) =
      ∫ x, (partialDeriv i (partialDeriv j u) x) ^ 2 := by
  have h₁ := integral_partial_mul_eq_neg_mul_partial
    (contDiff_partial hu i) (hasCompactSupport_partial hc i)
    (contDiff_partial (contDiff_partial hu j) j)
    (hasCompactSupport_partial (hasCompactSupport_partial hc j) j) i
  have h₂ := integral_partial_mul_eq_neg_mul_partial
    (contDiff_partial hu i) (hasCompactSupport_partial hc i)
    (contDiff_partial (contDiff_partial hu j) i)
    (hasCompactSupport_partial (hasCompactSupport_partial hc j) i) j
  rw [partial_comm (contDiff_partial hu j) i j] at h₁
  rw [partial_comm hu j i] at h₂
  simpa only [pow_two] using h₁.trans h₂.symm

theorem second_partial_eq_zero_of_notMem_tsupport
    {u : E → ℝ} {x : E} (hx : x ∉ tsupport u) (i j : Fin d) :
    partialDeriv i (partialDeriv j u) x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hx ((tsupport_partial_subset i (partialDeriv j u)).trans
    (tsupport_partial_subset j u) h)

private theorem hasCompactSupport_sq {v : E → ℝ} (hv : HasCompactSupport v) :
    HasCompactSupport (fun x => v x ^ 2) := by
  simpa only [pow_two, Pi.mul_def] using hv.mul_right (f' := v)

theorem integrable_hessianSq
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    Integrable (hessianSq u) volume := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((contDiff_partial (contDiff_partial hu j) i).continuous.pow 2).integrable_of_hasCompactSupport
    (hasCompactSupport_sq (hasCompactSupport_partial (hasCompactSupport_partial hc j) i))

theorem integrable_euclideanLaplacian_sq
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    Integrable (fun x => euclideanLaplacian u x ^ 2) volume := by
  have hl : Continuous (euclideanLaplacian u) :=
    continuous_finsetSum _ (fun i _ => (contDiff_partial (contDiff_partial hu i) i).continuous)
  have hs : HasCompactSupport (euclideanLaplacian u) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hnot
    apply hx
    simp [euclideanLaplacian, second_partial_eq_zero_of_notMem_tsupport hnot]
  exact (hl.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hs)

/-- No nontrivial constant is selected: the two genuine Lebesgue integrals
are exactly equal for every smooth compactly supported function. -/
theorem integral_euclideanLaplacian_sq_eq_hessianSq
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    (∫ x, euclideanLaplacian u x ^ 2) = ∫ x, hessianSq u x := by
  have hprod (i j : Fin d) : Integrable
      (fun x => partialDeriv i (partialDeriv i u) x * partialDeriv j (partialDeriv j u) x)
      volume :=
    ((contDiff_partial (contDiff_partial hu i) i).continuous.mul
      (contDiff_partial (contDiff_partial hu j) j).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_partial (hasCompactSupport_partial hc i) i).mul_right
  have hsq (i j : Fin d) : Integrable
      (fun x => (partialDeriv i (partialDeriv j u) x) ^ 2) volume :=
    ((contDiff_partial (contDiff_partial hu j) i).continuous.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_sq (hasCompactSupport_partial (hasCompactSupport_partial hc j) i))
  have hpoint (x : E) : euclideanLaplacian u x ^ 2 =
      ∑ i : Fin d, ∑ j : Fin d,
        partialDeriv i (partialDeriv i u) x * partialDeriv j (partialDeriv j u) x := by
    unfold euclideanLaplacian
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hprod i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hprod _ j)]
  simp_rw [integral_diagonal_second_mul hu hc]
  unfold hessianSq
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hsq i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hsq _ j)]

#print axioms integral_diagonal_second_mul
#print axioms integrable_hessianSq
#print axioms integrable_euclideanLaplacian_sq
#print axioms integral_euclideanLaplacian_sq_eq_hessianSq

end Yamabe3.Analysis.UniformElliptic
