import Yamabe3.Analysis.NativeHalfEndH4Regularity
import Yamabe3.Analysis.NativeOrbitWeakJacobian

/-! An actual H2 function satisfies the divergence equation of its own
weak second derivatives. The coefficient product rule is proved in the
weak sense, allowing the native geometric equation to enter the existing
elliptic bootstrap without assuming a smooth representative in advance. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def weakDivergenceSource (O : Set E) (A : E→Matrix (Fin d) (Fin d) ℝ) (u : E→ℝ) : E→ℝ :=
  fun x => -(∑i : Fin d,∑j : Fin d,
    (A x i j*chosenWeakPartial' 2 i (chosenWeakPartial' 2 j u O) O x+
      partialDeriv i (fun y => A y i j) x*chosenWeakPartial' 2 j u O x))

theorem weakEquation_weakDivergenceSource {O : Set E} (hO : IsOpen O)
    (A : E→Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀i j,ContDiff ℝ ∞ (fun x => A x i j)) {u : E→ℝ} (hu : MemWkp 2 2 u O) :
    WeakEquation O (matrixFlux A (fun j => chosenWeakPartial' 2 j u O)) (weakDivergenceSource O A u) := by
  let p := fun j => chosenWeakPartial' 2 j u O
  let q := fun i j => chosenWeakPartial' 2 i (p j) O
  let D := fun i x => ∑j : Fin d,(A x i j*q i j x+partialDeriv i (fun y => A y i j) x*p j x)
  have hp (j : Fin d) : LocallyIntegrable (p j) (volume.restrict O) :=
    (hu.chosenWeakPartial_mem j).memLp.locallyIntegrable (by norm_num)
  have hq (i j : Fin d) : LocallyIntegrable (q i j) (volume.restrict O) :=
    ((hu.chosenWeakPartial_mem j).chosenWeakPartial_mem i).memLp.locallyIntegrable (by norm_num)
  have hD (i : Fin d) : LocallyIntegrable (D i) (volume.restrict O) :=
    Poincare.Analysis.Elliptic.Iteration.locallyIntegrable_finset_sum Finset.univ (fun j _ =>
      (LocallyIntegrable.continuous_mul (hA i j).continuous (hq i j)).add
        (LocallyIntegrable.continuous_mul (contDiff_partial (hA i j) i).continuous (hp j)))
  have hd (i : Fin d) : HasWeakPartialDeriv i (D i) (matrixFlux A p i) O := by
    apply weakPartial_finset_sum Finset.univ
      (fun j _ => LocallyIntegrable.continuous_mul (hA i j).continuous (hp j))
      (fun j _ => (LocallyIntegrable.continuous_mul (hA i j).continuous (hq i j)).add
        (LocallyIntegrable.continuous_mul (contDiff_partial (hA i j) i).continuous (hp j)))
    intro j _
    exact (chosenWeakPartial'_isWeakPartial_of_mem (hu.chosenWeakPartial_mem j).memW1p i).mul_smooth
      hO (hA i j) (hp j) (hq i j)
  intro φ hφ hc hs
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_mul_partial_test
    (locallyIntegrable_matrixFlux (fun i j => (hA i j).continuous) hp i) hφ hc i)]
  have hi (i : Fin d) : (∫x in O,matrixFlux A p i x*partialDeriv i φ x)= -(∫x in O,D i x*φ x) := hd i φ hφ hc hs
  simp_rw [hi]
  rw [Finset.sum_neg_distrib]
  change -(∑i : Fin d,∫x in O,D i x*φ x)=∫x in O,(-(∑i : Fin d,D i x))*φ x
  simp_rw [neg_mul,Finset.sum_mul]
  rw [integral_neg,integral_finsetSum Finset.univ (fun i _ => integrable_mul_test (hD i) hφ hc)]

#print axioms weakEquation_weakDivergenceSource
end Yamabe3.Analysis.UniformElliptic
