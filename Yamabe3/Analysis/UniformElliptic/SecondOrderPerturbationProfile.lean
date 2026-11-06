import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.ProfileCalculus

/-!
# A second-order geometric error consumes exactly two Sobolev derivatives

This is an estimate for the literal differential expression, not an inverse
assumption. All coefficient jets through k are bounded by the displayed eta.
In dimension three the H2 source / H4 solution coefficient is exactly 91 eta.
The estimate also applies at k=4, so an H4-source / H6-solution choice can use
the existing pointwise embedding without introducing derivative loss.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory
open scoped ENNReal ContDiff BigOperators

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The actual nondivergence expression of a second-order perturbation. -/
def secondOrderPerturbation
    (a : Fin 3 → Fin 3 → E3 → ℝ) (b : Fin 3 → E3 → ℝ)
    (c v : E3 → ℝ) (x : E3) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, a i j x * partialDeriv i (partialDeriv j v) x) +
    (∑ i : Fin 3, b i x * partialDeriv i v x) + c x * v x

/-- The accumulated Leibniz coefficient is linear in the common jet bound. -/
theorem cutoffMultiplier_eq_mul_one (k : ℕ) (η : ℝ) :
    cutoffMultiplier k η = cutoffMultiplier k 1 * η := by
  simp only [cutoffMultiplier, Finset.sum_mul, mul_one]

/-- Uniform jets of the literal coefficients bound the actual second-order
error in H^k by the same function's H^(k+2) profile, on the same set. -/
theorem derivativeProfile_secondOrderPerturbation_le
    {Ω : Set E3} (hΩ : IsOpen Ω) (k : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (a : Fin 3 → Fin 3 → E3 → ℝ) (b : Fin 3 → E3 → ℝ) (c v : E3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ContDiff ℝ ∞ c)
    (hv : ContDiff ℝ ∞ v)
    (hajet : ∀ n ≤ k, ∀ x ∈ Ω, ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ n (a i j) x‖ ≤ η)
    (hbjet : ∀ n ≤ k, ∀ x ∈ Ω, ∀ i : Fin 3,
      ‖iteratedFDeriv ℝ n (b i) x‖ ≤ η)
    (hcjet : ∀ n ≤ k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ n c x‖ ≤ η) :
    derivativeProfile 2 Ω k (secondOrderPerturbation a b c v) ≤
      ENNReal.ofReal (13 * cutoffMultiplier k 1 * η) *
        derivativeProfile 2 Ω (k + 2) v := by
  let T := ENNReal.ofReal (cutoffMultiplier k η) * derivativeProfile 2 Ω (k + 2) v
  let principal : E3 → ℝ := fun x =>
    ∑ i : Fin 3, ∑ j : Fin 3, a i j x * partialDeriv i (partialDeriv j v) x
  let first : E3 → ℝ := fun x => ∑ i : Fin 3, b i x * partialDeriv i v x
  have hpartial (i j : Fin 3) :
      derivativeProfile 2 Ω k (partialDeriv i (partialDeriv j v)) ≤
        derivativeProfile 2 Ω (k + 2) v := by
    exact (derivativeProfile_partial_le k i (contDiff_partial hv j)).trans
      (by simpa only [Nat.add_assoc] using derivativeProfile_partial_le (k + 1) j hv)
  have haTerm (i j : Fin 3) :
      derivativeProfile 2 Ω k (fun x => a i j x * partialDeriv i (partialDeriv j v) x) ≤ T := by
    exact (derivativeProfile_mul_le hΩ (by norm_num : (1 : ℝ≥0∞) ≤ 2) k
      (ha i j) (contDiff_partial (contDiff_partial hv j) i) hη
      (fun n hn x hx => hajet n hn x hx i j)).trans
        (mul_le_mul_of_nonneg_left (hpartial i j) zero_le)
  have hbTerm (i : Fin 3) :
      derivativeProfile 2 Ω k (fun x => b i x * partialDeriv i v x) ≤ T := by
    exact (derivativeProfile_mul_le hΩ (by norm_num : (1 : ℝ≥0∞) ≤ 2) k
      (hb i) (contDiff_partial hv i) hη
      (fun n hn x hx => hbjet n hn x hx i)).trans
        (mul_le_mul_of_nonneg_left ((derivativeProfile_partial_le k i hv).trans
          (derivativeProfile_mono_order (by omega : k + 1 ≤ k + 2) v)) zero_le)
  have hcTerm : derivativeProfile 2 Ω k (fun x => c x * v x) ≤ T := by
    exact (derivativeProfile_mul_le hΩ (by norm_num : (1 : ℝ≥0∞) ≤ 2) k hc hv hη hcjet).trans
      (mul_le_mul_of_nonneg_left
        (derivativeProfile_mono_order (by omega : k ≤ k + 2) v) zero_le)
  have hpSmooth : ContDiff ℝ ∞ principal := by
    apply ContDiff.sum
    intro i _
    exact ContDiff.sum fun j _ => (ha i j).mul (contDiff_partial (contDiff_partial hv j) i)
  have hfSmooth : ContDiff ℝ ∞ first :=
    ContDiff.sum fun i _ => (hb i).mul (contDiff_partial hv i)
  have hpBound : derivativeProfile 2 Ω k principal ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, T := by
    apply (derivativeProfile_finset_sum_le hΩ (by norm_num : (1 : ℝ≥0∞) ≤ 2) k
      Finset.univ (fun i _ => ContDiff.sum fun j _ =>
        (ha i j).mul (contDiff_partial (contDiff_partial hv j) i))).trans
    apply Finset.sum_le_sum
    intro i _
    exact (derivativeProfile_finset_sum_le hΩ (by norm_num : (1 : ℝ≥0∞) ≤ 2) k
      Finset.univ (fun j _ => (ha i j).mul (contDiff_partial (contDiff_partial hv j) i))).trans
        (Finset.sum_le_sum fun j _ => haTerm i j)
  have hfBound : derivativeProfile 2 Ω k first ≤ ∑ _i : Fin 3, T := by
    exact (derivativeProfile_finset_sum_le hΩ (by norm_num : (1 : ℝ≥0∞) ≤ 2) k
      Finset.univ (fun i _ => (hb i).mul (contDiff_partial hv i))).trans
        (Finset.sum_le_sum fun i _ => hbTerm i)
  have hsum := derivativeProfile_add_le hΩ (by norm_num : (1 : ℝ≥0∞) ≤ 2) k
    (hpSmooth.add hfSmooth) (hc.mul hv)
  change derivativeProfile 2 Ω k (fun x => principal x + first x + c x * v x) ≤ _
  apply hsum.trans
  apply (add_le_add ((derivativeProfile_add_le hΩ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) k hpSmooth hfSmooth).trans
      (add_le_add hpBound hfBound)) hcTerm).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (13 : ℝ) * cutoffMultiplier k 1 * η = 13 * cutoffMultiplier k η by
    rw [cutoffMultiplier_eq_mul_one k η]; ring]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 13), ENNReal.ofReal_ofNat]
  dsimp only [T]
  ring

/-- The concrete H2 to H4 estimate needed to control a second-order error
in the same source space as an H2-source/H4-solution elliptic inverse. -/
theorem derivativeProfile_two_secondOrderPerturbation_le
    {Ω : Set E3} (hΩ : IsOpen Ω) {η : ℝ} (hη : 0 ≤ η)
    (a : Fin 3 → Fin 3 → E3 → ℝ) (b : Fin 3 → E3 → ℝ) (c v : E3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ContDiff ℝ ∞ c)
    (hv : ContDiff ℝ ∞ v)
    (hajet : ∀ n ≤ 2, ∀ x ∈ Ω, ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ n (a i j) x‖ ≤ η)
    (hbjet : ∀ n ≤ 2, ∀ x ∈ Ω, ∀ i : Fin 3,
      ‖iteratedFDeriv ℝ n (b i) x‖ ≤ η)
    (hcjet : ∀ n ≤ 2, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ n c x‖ ≤ η) :
    derivativeProfile 2 Ω 2 (secondOrderPerturbation a b c v) ≤
      ENNReal.ofReal (91 * η) * derivativeProfile 2 Ω 4 v := by
  have h := derivativeProfile_secondOrderPerturbation_le hΩ 2 hη a b c v
    ha hb hc hv hajet hbjet hcjet
  have hK : cutoffMultiplier 2 (1 : ℝ) = 7 := by
    norm_num [cutoffMultiplier, Finset.sum_range_succ]
  simpa only [hK, show (13 : ℝ) * 7 = 91 by norm_num] using h

#print axioms derivativeProfile_secondOrderPerturbation_le
#print axioms derivativeProfile_two_secondOrderPerturbation_le

end Yamabe3.Analysis.UniformElliptic
