import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Genuine jointly measurable representatives of L2-valued families

An arbitrary coeFn representative of a continuous L2-valued family need
not be jointly measurable. We construct one by a measurable, rapidly
convergent selection from actual simple L2-valued approximants. Summable
L2 errors force pointwise convergence almost everywhere on every slice.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay

variable {T X : Type*} [MeasurableSpace T] [MeasurableSpace X] {ν : Measure X}

/-- Actual joint representative; slice equality holds for every parameter,
with the null set allowed to depend on that parameter. -/
theorem exists_joint_L2_representative {U : T → Lp ℝ 2 ν}
    (hU : StronglyMeasurable U) :
    ∃ w : T × X → ℝ, StronglyMeasurable w ∧
      ∀ t, (fun x => w (t, x)) =ᵐ[ν] (U t : X → ℝ) := by
  classical
  have hUm := hU
  obtain ⟨s, hs⟩ := hU
  have hex (n : ℕ) (t : T) : ∃ j, dist (s j t) (U t) < (1 / 2 : ℝ) ^ n := by
    have h := (Metric.tendsto_atTop.mp (hs t)) ((1 / 2 : ℝ) ^ n) (by positivity)
    obtain ⟨j, hj⟩ := h
    exact ⟨j, hj j le_rfl⟩
  let sel (n : ℕ) (t : T) : ℕ := Nat.find (hex n t)
  let A (n : ℕ) (t : T) : Lp ℝ 2 ν := s (sel n t) t
  have hA (n : ℕ) (t : T) : dist (A n t) (U t) < (1 / 2 : ℝ) ^ n :=
    Nat.find_spec (hex n t)
  have hraw (j : ℕ) : Measurable (fun z : T × X => (s j z.1 : Lp ℝ 2 ν) z.2) := by
    exact ((s j).comp Prod.fst measurable_fst).measurable_bind
      (fun f z => (f : Lp ℝ 2 ν) z.2)
      (fun f => (Lp.stronglyMeasurable f).measurable.comp measurable_snd)
  have hAm (n : ℕ) : Measurable (fun z : T × X => A n z.1 z.2) := by
    apply Measurable.find hraw
      (fun j => (measurableSet_lt (((s j).stronglyMeasurable.dist hUm).measurable)
        measurable_const).preimage measurable_fst)
      (fun z => hex n z.1)
  let w : T × X → ℝ := fun z => limUnder atTop (fun n => A n z.1 z.2)
  have hwm : StronglyMeasurable w :=
    StronglyMeasurable.limUnder (fun n => (hAm n).stronglyMeasurable)
  refine ⟨w, hwm, fun t => ?_⟩
  have hsum : (∑' n : ℕ, eLpNorm ((A n t : X → ℝ) - (U t : X → ℝ)) 2 ν) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [← Lp.edist_def, Lp.edist_dist]
        exact ENNReal.ofReal_le_ofReal (hA n t).le
      _ < ∞ := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).tsum_ofReal_lt_top
  have hae := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ENNReal) ≤ 2)
    (fun n => (Lp.aestronglyMeasurable (A n t)).sub (Lp.aestronglyMeasurable (U t))) hsum
  filter_upwards [hae] with x hx
  have hsub : Tendsto (fun n => A n t x - U t x) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hx.tendsto_atTop_zero
  have hlim : Tendsto (fun n => A n t x) atTop (𝓝 (U t x)) := by
    simpa only [sub_add_cancel, zero_add] using hsub.add_const (U t x)
  exact hlim.limUnder_eq

/-- Every continuous real-L2-valued curve has a genuine joint representative,
without a countability assumption on the full L2 space. -/
theorem exists_joint_L2_representative_of_continuous {U : ℝ → Lp ℝ 2 ν}
    (hU : Continuous U) :
    ∃ w : ℝ × X → ℝ, StronglyMeasurable w ∧
      ∀ t, (fun x => w (t, x)) =ᵐ[ν] (U t : X → ℝ) :=
  exists_joint_L2_representative hU.stronglyMeasurable

/-- The square integral of each genuine slice is exactly the Hilbert norm. -/
theorem joint_L2_integral_sq {U : ℝ → Lp ℝ 2 ν} {w : ℝ × X → ℝ}
    (hae : ∀ t, (fun x => w (t, x)) =ᵐ[ν] (U t : X → ℝ)) (t : ℝ) :
    (∫ x, w (t, x) ^ 2 ∂ν) = ‖U t‖ ^ 2 := by
  calc
    _ = ∫ x, U t x ^ 2 ∂ν := by
      apply integral_congr_ae
      filter_upwards [hae t] with x hx
      rw [hx]
    _ = inner ℝ (U t) (U t) := by
      simp only [L2.inner_def, RCLike.inner_apply, conj_trivial, sq]
    _ = ‖U t‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- Actual local product L2 follows from curve continuity and Fubini. -/
theorem joint_L2_memLp_on_interval [SFinite ν] {U : ℝ → Lp ℝ 2 ν}
    (hU : Continuous U) {w : ℝ × X → ℝ} (hwm : StronglyMeasurable w)
    (hae : ∀ t, (fun x => w (t, x)) =ᵐ[ν] (U t : X → ℝ)) (a b : ℝ) :
    MemLp w 2 ((volume.restrict (Icc a b)).prod ν) := by
  apply (memLp_two_iff_integrable_sq hwm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hwm.pow 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((Lp.memLp (U t)).ae_eq (hae t).symm).integrable_sq
  · have heq : (fun t => ∫ x, ‖w (t, x) ^ 2‖ ∂ν) = fun t => ‖U t‖ ^ 2 := by
      funext t
      have hn : (fun x => ‖w (t, x) ^ 2‖) = fun x => w (t, x) ^ 2 := by
        funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (w (t, x)))]
      rw [hn]
      exact joint_L2_integral_sq hae t
    change Integrable (fun t => ∫ x, ‖w (t, x) ^ 2‖ ∂ν) (volume.restrict (Icc a b))
    rw [heq]
    exact (hU.norm.pow 2).integrableOn_Icc

end Yamabe3.Analysis.Delaunay
