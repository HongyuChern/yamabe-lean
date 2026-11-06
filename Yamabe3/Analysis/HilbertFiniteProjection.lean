import Yamabe3.Analysis.HilbertIntegralExpansion
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Logic.Encodable.Basic

/-!
# Genuine finite spectral approximations on compact time intervals

Finite orthogonal projections have norm at most one. An actual countable
exhaustion of the basis therefore converges in the true Hilbert norm at
all times, and dominated convergence gives the local time-L2 approximation
needed by the native finite-mode energy argument. No interchange of a
spectral sum with a time supremum is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual finite spectral projection in the genuine Hilbert space. -/
def finiteHilbertProjection (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H) : H :=
  ∑ i ∈ s, inner ℝ (b i) x • b i

theorem finiteHilbertProjection_norm_sq (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H) :
    ‖finiteHilbertProjection b s x‖ ^ 2 = ∑ i ∈ s, ‖inner ℝ (b i) x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  unfold finiteHilbertProjection
  rw [b.orthonormal.inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [conj_trivial, Real.norm_eq_abs]
  change inner ℝ (b i) x * inner ℝ (b i) x = |inner ℝ (b i) x| ^ 2
  rw [sq_abs]
  ring

theorem finiteHilbertProjection_norm_le (b : HilbertBasis ι ℝ H) (s : Finset ι) (x : H) :
    ‖finiteHilbertProjection b s x‖ ≤ ‖x‖ := by
  have h := b.orthonormal.sum_inner_products_le (s := s) x
  rw [← finiteHilbertProjection_norm_sq] at h
  nlinarith [norm_nonneg (finiteHilbertProjection b s x), norm_nonneg x]

theorem continuous_finiteHilbertProjection (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    Continuous (finiteHilbertProjection b s) := by
  unfold finiteHilbertProjection
  apply continuous_finsetSum
  intro i hi
  exact (innerSL ℝ (b i)).continuous.smul continuous_const

theorem finiteHilbertProjection_sub_norm_sq_le (b : HilbertBasis ι ℝ H)
    (s : Finset ι) (x : H) : ‖finiteHilbertProjection b s x - x‖ ^ 2 ≤ 4 * ‖x‖ ^ 2 := by
  have hn : ‖finiteHilbertProjection b s x - x‖ ≤ 2 * ‖x‖ :=
    (norm_sub_le _ _).trans (by linarith [finiteHilbertProjection_norm_le b s x])
  nlinarith [norm_nonneg (finiteHilbertProjection b s x - x), norm_nonneg x]

/-- The exhaustion is constructed from an actual encoding of the countable
index. It is independent of the curve or of the compact time interval. -/
theorem exists_finite_basis_exhaustion [Countable ι] :
    ∃ s : ℕ → Finset ι, Monotone s ∧ Tendsto s atTop atTop := by
  classical
  let := Encodable.ofCountable ι
  let s : ℕ → Finset ι := fun n => (Finset.range n).preimage Encodable.encode
    Encodable.encode_injective.injOn
  refine ⟨s, ?_, ?_⟩
  · intro m n hmn i hi
    apply Finset.mem_preimage.mpr
    exact Finset.range_mono hmn (Finset.mem_preimage.mp hi)
  · exact (tendsto_finset_preimage_atTop_atTop Encodable.encode_injective).comp tendsto_finset_range

theorem finiteHilbertProjection_tendsto (b : HilbertBasis ι ℝ H)
    {s : ℕ → Finset ι} (hs : Tendsto s atTop atTop) (x : H) :
    Tendsto (fun n => finiteHilbertProjection b (s n) x) atTop (𝓝 x) := by
  have h : HasSum (fun i => inner ℝ (b i) x • b i) x := by
    simpa only [HilbertBasis.repr_apply_apply] using b.hasSum_repr x
  exact h.comp hs

/-- Actual compact-time L2 convergence, with a common integrable dominating
function obtained from the norm-one finite projections. -/
theorem finiteHilbertProjection_integral_error_tendsto (b : HilbertBasis ι ℝ H)
    {s : ℕ → Finset ι} (hs : Tendsto s atTop atTop)
    {U : ℝ → H} (hU : Continuous U) (a c : ℝ) :
    Tendsto (fun n => ∫ t in Icc a c, ‖finiteHilbertProjection b (s n) (U t) - U t‖ ^ 2)
      atTop (𝓝 0) := by
  have hbound : Integrable (fun t : ℝ => 4 * ‖U t‖ ^ 2) (volume.restrict (Icc a c)) := by
    convert ((hU.norm.pow 2).const_mul 4).integrableOn_Icc (μ := volume) (a := a) (b := c) using 1 <;> rfl
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc a c)) (fun t : ℝ => 4 * ‖U t‖ ^ 2)
    (F := fun n t => ‖finiteHilbertProjection b (s n) (U t) - U t‖ ^ 2)
    (f := fun _ => (0 : ℝ))
    (fun n => (((continuous_finiteHilbertProjection b (s n)).comp hU).sub hU).norm.pow 2
      |>.aestronglyMeasurable)
    hbound
    (fun n => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact finiteHilbertProjection_sub_norm_sq_le b (s n) (U t))
    (Eventually.of_forall fun t => by
      simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((finiteHilbertProjection_tendsto b hs (U t)).sub
          (tendsto_const_nhds (x := U t))).norm.pow 2)
  simpa only [integral_zero] using h

/-- One fixed finite exhaustion works for every continuous curve and every
bounded time interval, and all approximants satisfy the genuine pointwise
Hilbert norm bound. -/
theorem exists_hilbert_finite_approximation [Countable ι] (b : HilbertBasis ι ℝ H) :
    ∃ s : ℕ → Finset ι, Monotone s ∧ Tendsto s atTop atTop ∧
      (∀ n x, ‖finiteHilbertProjection b (s n) x‖ ≤ ‖x‖) ∧
      (∀ x, Tendsto (fun n => finiteHilbertProjection b (s n) x) atTop (𝓝 x)) ∧
      ∀ (U : ℝ → H), Continuous U → ∀ a c : ℝ,
        Tendsto (fun n => ∫ t in Icc a c,
          ‖finiteHilbertProjection b (s n) (U t) - U t‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨s, hm, hs⟩ := exists_finite_basis_exhaustion (ι := ι)
  exact ⟨s, hm, hs, fun n x => finiteHilbertProjection_norm_le b (s n) x,
    finiteHilbertProjection_tendsto b hs,
    fun U hU a c => finiteHilbertProjection_integral_error_tendsto b hs hU a c⟩

end Yamabe3.Analysis.Delaunay
