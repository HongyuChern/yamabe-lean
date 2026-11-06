import Yamabe3.Analysis.BoundaryReflectionWeakDerivative
import Yamabe3.Analysis.BoundaryH2SobolevEstimate

/-! Finite moment matching produces an actual bounded all-order weak
Sobolev extension. Every derivative is proved by a distributional identity;
the extension is one fixed linear function, not independently chosen jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.BoundaryTangential Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem reflectionDerivativeCoeffs_moments (k : ℕ) (r c : ι → ℝ)
    (hm : ∀ q : ℕ, q < k+1 → ∑ j, c j * (-r j)^q = 1) (i : Fin d) :
    ∀ q : ℕ, q < k → ∑ j, reflectionDerivativeCoeffs r c i j * (-r j)^q = 1 := by
  intro q hq
  by_cases hi : i = 0
  · subst i
    convert hm (q+1) (by omega) using 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [reflectionDerivativeCoeffs, normalFactor, ite_true, pow_succ]
    ring
  · simpa only [reflectionDerivativeCoeffs, normalFactor, if_neg hi, mul_one] using hm q (by omega)

theorem exists_finiteReflection_sobolev_bound (k : ℕ)
    (r : ι → ℝ) (hr : ∀ j, 0 < r j) (c : ι → ℝ)
    (hm : ∀ q : ℕ, q < k → ∑ j, c j * (-r j)^q = 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ,
      MemWkp k 2 u (halfSpace d) →
      MemWkp k 2 (finiteReflection r hr c u) univ ∧
      iteratedWeakSobolevNorm k 2 (finiteReflection r hr c u) univ ≤
        C * iteratedWeakSobolevNorm k 2 u (halfSpace d) := by
  classical
  induction k generalizing c with
  | zero =>
    refine ⟨finiteReflectionL2Bound r c, finiteReflectionL2Bound_ne_top r c, ?_⟩
    intro u hu
    refine ⟨?_, ?_⟩
    · simpa only [MemWkp.zero_iff_memLp, Measure.restrict_univ] using memLp_finiteReflection r hr c hu
    · simpa only [wkpNorm_zero, Measure.restrict_univ] using eLpNorm_finiteReflection_le r hr c hu
  | succ k ih =>
    have hm0 : ∑ j, c j = 1 := by simpa only [pow_zero, mul_one] using hm 0 (by omega)
    choose C hC hb using fun i : Fin d => ih (reflectionDerivativeCoeffs r c i)
      (reflectionDerivativeCoeffs_moments k r c hm i)
    refine ⟨finiteReflectionL2Bound r c + ∑ i, C i,
      ENNReal.add_ne_top.mpr ⟨finiteReflectionL2Bound_ne_top r c,
        ENNReal.sum_ne_top.mpr (fun i _ => hC i)⟩, ?_⟩
    intro u hu
    let g (i : Fin d) := finiteReflection r hr (reflectionDerivativeCoeffs r c i)
      (chosenWeakPartial' 2 i u (halfSpace d))
    have hg (i : Fin d) := hb i _ (hu.chosenWeakPartial_mem i)
    have hw (i : Fin d) : HasWeakPartialDeriv i (g i) (finiteReflection r hr c u) univ :=
      hasWeakPartialDeriv_finiteReflection r hr c hm0 i hu.memLp
        (chosenWeakPartial'_memLp_of_mem hu.memW1p i)
        (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
    have hext : MemWkp (k+1) 2 (finiteReflection r hr c u) univ :=
      memWkp_succ_of_weakDerivatives isOpen_univ (by norm_num)
        (by simpa only [Measure.restrict_univ] using memLp_finiteReflection r hr c hu.memLp)
        (fun i => (hg i).1) hw
    have heq (i : Fin d) : chosenWeakPartial' 2 i (finiteReflection r hr c u) univ =ᵐ[volume.restrict univ] g i :=
      HasWeakPartialDeriv.ae_eq isOpen_univ
        (chosenWeakPartial'_isWeakPartial_of_mem hext.memW1p i) (hw i)
        ((chosenWeakPartial'_memLp_of_mem hext.memW1p i).locallyIntegrable (by norm_num))
        ((hg i).1.memLp.locallyIntegrable (by norm_num))
    have hgn (i : Fin d) : iteratedWeakSobolevNorm k 2 (g i) univ ≤
        C i * iteratedWeakSobolevNorm (k+1) 2 u (halfSpace d) :=
      (hg i).2.trans (mul_le_mul le_rfl
        (wkpNorm_chosenWeakPartial_le_wkpNorm_succ k 2 u (halfSpace d) i) zero_le zero_le)
    refine ⟨hext, ?_⟩
    rw [wkpNorm_succ_eq k]
    calc
      _ ≤ finiteReflectionL2Bound r c * iteratedWeakSobolevNorm (k+1) 2 u (halfSpace d) +
          ∑ i : Fin d, C i * iteratedWeakSobolevNorm (k+1) 2 u (halfSpace d) := by
        apply add_le_add
        · simp only [Measure.restrict_univ]
          exact (eLpNorm_finiteReflection_le r hr c hu.memLp).trans
            (mul_le_mul le_rfl (by
              rw [← wkpNorm_zero]
              exact wkpNorm_mono_order (Nat.zero_le _) u (halfSpace d)) zero_le zero_le)
        · apply Finset.sum_le_sum
          intro i _
          rw [wkpNorm_congr_ae (k := k) (by norm_num : (1:ℝ≥0∞) ≤ 2) isOpen_univ (heq i)]
          exact hgn i
      _ = _ := by rw [add_mul, Finset.sum_mul]

#print axioms exists_finiteReflection_sobolev_bound
end Yamabe3.Analysis.UniformElliptic
