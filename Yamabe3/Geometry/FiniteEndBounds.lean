import Yamabe3.Geometry.CylindricalCompleteness
import Yamabe3.Analysis.FinitePunctureCompleteness

/-!
# Compact-background bounds from actual cylindrical end lower bounds

The finite-puncture completeness argument needs global comparisons with
complete one-puncture cylindrical metrics. Local lower bounds at every
deleted point and actual smoothness on the complement provide these
comparisons by a finite neighborhood subcover of the compact background.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology BigOperators Classical

namespace Yamabe3.Geometry.CylindricalCompleteness

open PoincareMT Yamabe3.Parametrix GreenMass.PuncturedEnd

theorem exists_positive_bound_of_local_upper_bounds
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (f : X → ℝ)
    (h : ∀ p : X, ∃ C : ℝ, ∀ᶠ y in 𝓝 p, f y ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : X, f y ≤ C := by
  classical
  choose C hC using h
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (fun p => {y | f y ≤ C p}) hC
  let B : ℝ := ∑ p ∈ s, |C p|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B + 1, by linarith, ?_⟩
  intro y
  have hym : y ∈ ⋃ p ∈ s, {z | f z ≤ C p} := by rw [hs]; trivial
  obtain ⟨p, hp, hy⟩ := mem_iUnion₂.mp hym
  have hsingle : |C p| ≤ B := Finset.single_le_sum (fun q _ => abs_nonneg (C q)) hp
  exact hy.trans ((le_abs_self (C p)).trans (hsingle.trans (by linarith)))

variable {M : Type*} [TopologicalSpace M]

/-- A genuine chart neighborhood of its center, expressed by the actual
inverse chart. No surjectivity outside the chart target is used. -/
theorem eventually_in_centered_chart
    (e : OpenPartialHomeomorph E M) (h0 : (0 : E) ∈ e.source)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ y in 𝓝 (e 0), y ∈ e.target ∧ ‖e.symm y‖ < r := by
  have ht : e 0 ∈ e.target := e.map_source h0
  have hc : ContinuousAt e.symm (e 0) :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds ht)
  have hb : ball (0 : E) r ∈ 𝓝 (e.symm (e 0)) := by
    rw [e.left_inv h0]
    exact ball_mem_nhds _ hr
  filter_upwards [e.open_target.mem_nhds ht, hc.eventually hb] with y hy hby
  exact ⟨hy, by simpa using hby⟩

theorem cylindrical_ratio_bound {r c U : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c)
    (hl : c * r⁻¹ ≤ U ^ 2) :
    (1 + r⁻¹) / U ^ 2 ≤ 2 / c := by
  have hU : 0 < U ^ 2 := (mul_pos hc (inv_pos.mpr hr)).trans_le hl
  apply (div_le_iff₀ hU).mpr
  have h1 : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  have h2 := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 / c by positivity)
  have hid : (2 / c) * (c * r⁻¹) = 2 * r⁻¹ := by field_simp
  rw [hid] at h2
  linarith

variable [T3Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

/-- The actual cutoff Newton numerator at one selected pole is bounded
globally by a fixed multiple of u squared, once u has cylindrical lower
bounds at every prescribed pole. -/
theorem exists_global_cylindrical_comparison
    (Λ : Finset M) (u : M → ℝ)
    (hu : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (Λ : Set M)ᶜ)
    (hupos : ∀ y ∉ Λ, 0 < u y)
    (e : M → OpenPartialHomeomorph E M) (χ : M → ContDiffBump (0 : E))
    (h0 : ∀ q ∈ Λ, (0 : E) ∈ (e q).source)
    (hep : ∀ q ∈ Λ, e q 0 = q)
    (hei : ∀ q ∈ Λ, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e q).symm (e q).target)
    (hχ : ∀ q ∈ Λ, tsupport (χ q) ⊆ (e q).source)
    (c r : M → ℝ) (hc : ∀ q ∈ Λ, 0 < c q) (hr : ∀ q ∈ Λ, 0 < r q)
    (hlower : ∀ q ∈ Λ, ∀ x : E, e q x ∉ Λ → 0 < ‖x‖ → ‖x‖ < r q →
      c q * ‖x‖⁻¹ ≤ u (e q x) ^ 2)
    (p : M) (hp : p ∈ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∉ Λ, 1 + singular (e p) (χ p) y ≤ C * u y ^ 2 := by
  classical
  let N : M → ℝ := fun y => 1 + singular (e p) (χ p) y
  let F : M → ℝ := fun y => if y ∈ Λ then 0 else N y / u y ^ 2
  have hNpos : ∀ y, 0 < N y := by
    intro y
    have hs := singular_nonneg (e p) (χ p) y
    dsimp only [N]
    linarith
  have hlocal : ∀ q : M, ∃ C : ℝ, ∀ᶠ y in 𝓝 q, F y ≤ C := by
    intro q
    by_cases hq : q ∈ Λ
    · let δ := min (r q) (min (χ p).rIn 1)
      have hδ : 0 < δ := lt_min (hr q hq) (lt_min (χ p).rIn_pos zero_lt_one)
      have hδr : δ ≤ r q := min_le_left _ _
      have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
      have hδχ : δ ≤ (χ p).rIn := (min_le_right _ _).trans (min_le_left _ _)
      have hnear : ∀ᶠ y in 𝓝 q, y ∈ (e q).target ∧ ‖(e q).symm y‖ < δ := by
        simpa only [hep q hq] using eventually_in_centered_chart (e q) (h0 q hq) hδ
      by_cases hqp : q = p
      · subst q
        refine ⟨2 / c p, ?_⟩
        filter_upwards [hnear] with y hy
        by_cases hyΛ : y ∈ Λ
        · simp only [F, if_pos hyΛ]
          exact (div_pos (by norm_num) (hc p hp)).le
        · let x := (e p).symm y
          have hxy : e p x = y := (e p).right_inv hy.1
          have hx0 : x ≠ 0 := by
            intro hz
            exact hyΛ ((hxy.symm.trans (hz ▸ hep p hp)) ▸ hp)
          have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
          have hl := hlower p hp x (by simpa only [hxy] using hyΛ) hxn (hy.2.trans_le hδr)
          have hS : singular (e p) (χ p) y = ‖x‖⁻¹ := by
            rw [← hxy]
            exact singular_eq_inv_norm_near_center (e p) (χ p) (hχ p hp)
              (by simpa only [mem_closedBall, dist_zero_right] using (hy.2.trans_le hδχ).le)
          simp only [F, if_neg hyΛ, N, hS]
          rw [hxy] at hl
          exact cylindrical_ratio_bound hxn (hy.2.le.trans hδ1) (hc p hp) hl
      · have hNc : ContinuousAt N q := by
          apply continuousAt_const.add
          apply (contMDiffAt_singular (e p) (hei p hp) (χ p) (hχ p hp) ?_).continuousAt
          simpa only [hep p hp] using hqp
        let B := N q + 1
        have hB : 0 < B := by dsimp only [B]; linarith [hNpos q]
        have hNb : ∀ᶠ y in 𝓝 q, N y < B :=
          hNc.eventually (Iio_mem_nhds (by dsimp only [B]; linarith))
        refine ⟨B / c q, ?_⟩
        filter_upwards [hnear, hNb] with y hy hNy
        by_cases hyΛ : y ∈ Λ
        · simp only [F, if_pos hyΛ]
          exact (div_pos hB (hc q hq)).le
        · let x := (e q).symm y
          have hxy : e q x = y := (e q).right_inv hy.1
          have hx0 : x ≠ 0 := by
            intro hz
            exact hyΛ ((hxy.symm.trans (hz ▸ hep q hq)) ▸ hq)
          have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
          have hl := hlower q hq x (by simpa only [hxy] using hyΛ) hxn (hy.2.trans_le hδr)
          rw [hxy] at hl
          have hU : c q ≤ u y ^ 2 := by
            have hinv : 1 ≤ ‖x‖⁻¹ := (one_le_inv₀ hxn).mpr (hy.2.le.trans hδ1)
            nlinarith only [hl, mul_le_mul_of_nonneg_left hinv (hc q hq).le]
          simp only [F, if_neg hyΛ]
          exact div_le_div₀ hB.le hNy.le (hc q hq) hU
    · have hqp : q ≠ p := by intro h; exact hq (h ▸ hp)
      have hNc : ContinuousAt N q := by
        apply continuousAt_const.add
        apply (contMDiffAt_singular (e p) (hei p hp) (χ p) (hχ p hp) ?_).continuousAt
        simpa only [hep p hp] using hqp
      have huc := (hu.contMDiffAt (Λ.finite_toSet.isClosed.isOpen_compl.mem_nhds hq)).continuousAt
      have hratio : ContinuousAt (fun y => N y / u y ^ 2) q :=
        hNc.div (huc.pow 2) (pow_ne_zero 2 (hupos q hq).ne')
      refine ⟨N q / u q ^ 2 + 1, ?_⟩
      have hb : ∀ᶠ y in 𝓝 q, N y / u y ^ 2 < N q / u q ^ 2 + 1 :=
        hratio.eventually (Iio_mem_nhds (by linarith))
      filter_upwards [Λ.finite_toSet.isClosed.isOpen_compl.mem_nhds hq, hb] with y hy hby
      have hyΛ : y ∉ Λ := hy
      simpa only [F, if_neg hyΛ] using hby.le
  obtain ⟨C, hC, hbound⟩ := exists_positive_bound_of_local_upper_bounds F hlocal
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hb : N y / u y ^ 2 ≤ C := by simpa only [F, if_neg hy] using hbound y
  exact (div_le_iff₀ (sq_pos_of_pos (hupos y hy))).mp hb

#print axioms exists_positive_bound_of_local_upper_bounds
#print axioms eventually_in_centered_chart
#print axioms cylindrical_ratio_bound
#print axioms exists_global_cylindrical_comparison

end Yamabe3.Geometry.CylindricalCompleteness
