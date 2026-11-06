import Yamabe3.Analysis.GreenLocalH2
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Embedding.MorreyHigherOrder
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Embedding.ExponentIteration
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# A genuine half-Hölder estimate from coordinate H2

The exponent is obtained from the proved W2,2 -> W1,6 step and the uniform
smooth Morrey estimate in dimension three. Smooth compact approximations
have a common gradient L6 bound. An almost-everywhere convergent subsequence
preserves the Hölder inequality, and continuity of the given representative
extends it to every pair of points. No quantitative regularity is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Metric Filter
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.GreenRegularPart

open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanMorrey

abbrev E := EuclideanSpace ℝ (Fin 3)

private theorem le_on_open_of_ae_le {O : Set E} (hO : IsOpen O)
    {f g : E → ℝ} (hf : ContinuousOn f O) (hg : ContinuousOn g O)
    (h : ∀ᵐ x ∂volume.restrict O, f x ≤ g x) : ∀ x ∈ O, f x ≤ g x := by
  have heq : (fun x => max (f x) (g x)) =ᵐ[volume.restrict O] g := by
    filter_upwards [h] with x hx
    exact max_eq_right hx
  have hh := Measure.eqOn_open_of_ae_eq (μ := volume) heq hO (hf.sup hg) hg
  intro x hx
  exact max_eq_right_iff.mp (hh hx)

/-- Smooth W1,6 compact approximants carry a uniform genuine half-Hölder
bound to their continuous almost-everywhere limit. -/
theorem holder_half_of_smooth_approx
    {x₀ : E} {R : ℝ} (hR : 0 < R) {u : E → ℝ}
    (hu : ContinuousOn u (ball x₀ R))
    (φ : ℕ → E → ℝ) (hφ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (B : ℝ) (hB : 0 ≤ B)
    (hgrad : ∀ n, (eLpNorm (fun y => ‖fderiv ℝ (φ n) y‖) 6
      (volume.restrict (ball x₀ R))).toReal ≤ B)
    (hconv : ∀ᵐ x ∂volume.restrict (ball x₀ R),
      Tendsto (fun n => φ n x) atTop (𝓝 (u x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
      ‖u x - u y‖ ≤ C * dist x y ^ (1 / 2 : ℝ) := by
  obtain ⟨C₀, hC₀, hMorrey⟩ := smooth_morrey_pair_bound_uniform
    (d := 3) (p := 6) (by norm_num) hR
  let C : ℝ := C₀ * B
  have hC : 0 ≤ C := mul_nonneg hC₀ hB
  have hbound (n : ℕ) {x y : E} (hx : x ∈ ball x₀ (R / 2))
      (hy : y ∈ ball x₀ (R / 2)) :
      ‖φ n x - φ n y‖ ≤ C * dist x y ^ (1 / 2 : ℝ) := by
    have h := hMorrey (hφ n) hx hy
    norm_num at h
    calc
      _ ≤ C₀ * dist x y ^ (1 / 2 : ℝ) *
          (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) 6
            (volume.restrict (ball x₀ R))).toReal := by
            simpa only [Real.norm_eq_abs, eLpNorm_norm] using h
      _ ≤ C₀ * dist x y ^ (1 / 2 : ℝ) * B :=
        mul_le_mul_of_nonneg_left (hgrad n)
          (mul_nonneg hC₀ (Real.rpow_nonneg dist_nonneg _))
      _ = C * dist x y ^ (1 / 2 : ℝ) := by dsimp [C]; ring
  have hsmall : ball x₀ (R / 2) ⊆ ball x₀ R := ball_subset_ball (by linarith)
  have huc := hu.mono hsmall
  have hconv' := ae_restrict_of_ae_restrict_of_subset hsmall hconv
  have hAE : ∀ᵐ x ∂volume.restrict (ball x₀ (R / 2)),
      ∀ y ∈ ball x₀ (R / 2), ‖u x - u y‖ ≤ C * dist x y ^ (1 / 2 : ℝ) := by
    filter_upwards [hconv', ae_restrict_mem measurableSet_ball] with x hx hxball
    apply le_on_open_of_ae_le isOpen_ball
      ((continuousOn_const.sub huc).norm)
      (continuousOn_const.mul ((continuous_const.dist continuous_id).rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))).continuousOn)
    filter_upwards [hconv', ae_restrict_mem measurableSet_ball] with y hy hyball
    exact le_of_tendsto ((hx.sub hy).norm) (Eventually.of_forall fun n => hbound n hxball hyball)
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hAEy : ∀ᵐ z ∂volume.restrict (ball x₀ (R / 2)),
      ‖u z - u y‖ ≤ C * dist z y ^ (1 / 2 : ℝ) := hAE.mono fun z hz => hz y hy
  exact le_on_open_of_ae_le isOpen_ball ((huc.sub continuousOn_const).norm)
    (continuousOn_const.mul ((continuous_id.dist continuous_const).rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))).continuousOn) hAEy x hx

/-- The chosen W1,6 approximation has a common gradient bound; its limit
inequality is a theorem about the actual continuous Sobolev representative. -/
theorem holder_half_of_continuous_memW1Six_compact
    {x₀ : E} {R : ℝ} (hR : 0 < R) {u : E → ℝ}
    (hu : MemWkp 1 6 u (ball x₀ R)) (huc : ContinuousOn u (ball x₀ R))
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ ball x₀ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2),
      ‖u x - u y‖ ≤ C * dist x y ^ (1 / 2 : ℝ) := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ 6 := by norm_num
  have hpTop : (6 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  have happrox : ∀ n : ℕ, ∃ φ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ ball x₀ R ∧
      iteratedWeakSobolevNorm 1 6 (fun y => u y - φ y) (ball x₀ R) ≤
        ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    exact MemWkp.exists_smooth_compactSupport_approx isOpen_ball 1 6 hp hpTop
      hu hc hs _ (by positivity)
  choose φ hφ hφc hφs hclose using happrox
  have hφW (n : ℕ) : MemWkp 1 6 (φ n) (ball x₀ R) :=
    MemWkp_of_smooth_compactSupport isOpen_ball (hφ n) (hφc n) (hφs n) hp 1
  let N : ℝ≥0∞ := iteratedWeakSobolevNorm 1 6 u (ball x₀ R) + 1
  have hN : N ≠ (⊤ : ℝ≥0∞) := ENNReal.add_ne_top.mpr ⟨(wkpNorm_lt_top_of_memWkp hu).ne, by simp⟩
  have hnorm (n : ℕ) : iteratedWeakSobolevNorm 1 6 (φ n) (ball x₀ R) ≤ N := by
    have hdiff : MemWkp 1 6 (fun y => u y - φ n y) (ball x₀ R) :=
      MemWkp.sub hp isOpen_ball hu (hφW n)
    have hneg := MemWkp.neg hp isOpen_ball hdiff
    have htri := wkpNorm_add_le hp isOpen_ball hu hneg
    have hdecomp : (fun y => u y + -(u y - φ n y)) = φ n := by funext y; ring
    rw [hdecomp] at htri
    have hn : iteratedWeakSobolevNorm 1 6 (fun y => -(u y - φ n y)) (ball x₀ R) =
        iteratedWeakSobolevNorm 1 6 (fun y => u y - φ n y) (ball x₀ R) := by
      have he : (fun y => -(u y - φ n y)) = fun y => (-1 : ℝ) * (u y - φ n y) := by
        funext y; ring
      rw [he, wkpNorm_const_smul hp isOpen_ball hdiff (-1)]
      simp
    rw [hn] at htri
    have herr : iteratedWeakSobolevNorm 1 6 (fun y => u y - φ n y) (ball x₀ R) ≤ 1 := by
      apply (hclose n).trans
      apply ENNReal.ofReal_le_one.mpr
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact htri.trans (add_le_add le_rfl herr)
  have hgrad (n : ℕ) : (eLpNorm (fun y => ‖fderiv ℝ (φ n) y‖) 6
      (volume.restrict (ball x₀ R))).toReal ≤ N.toReal := by
    apply ENNReal.toReal_mono hN
    have hcNorm := eLpNorm_iteratedFDeriv_le_wkpNorm isOpen_ball hp 1
      (hφ n) (hφc n) (hφs n)
    have hsingle : eLpNorm (fun y => ‖iteratedFDeriv ℝ 1 (φ n) y‖) 6
        (volume.restrict (ball x₀ R)) ≤
        ∑ j ∈ Finset.range (1 + 1), eLpNorm (fun y => ‖iteratedFDeriv ℝ j (φ n) y‖) 6
          (volume.restrict (ball x₀ R)) :=
      Finset.single_le_sum (f := fun j => eLpNorm (fun y => ‖iteratedFDeriv ℝ j (φ n) y‖) 6
        (volume.restrict (ball x₀ R))) (fun j hj => zero_le)
        (by decide : 1 ∈ Finset.range (1 + 1))
    simpa only [norm_iteratedFDeriv_one] using hsingle.trans (hcNorm.trans (hnorm n))
  have hLpbound (n : ℕ) : eLpNorm (φ n - u) 6 (volume.restrict (ball x₀ R)) ≤
      ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    rw [eLpNorm_sub_comm]
    have h := wkpNorm_mono_order (p := 6) (by omega : 0 ≤ 1) (u - φ n) (ball x₀ R)
    rw [wkpNorm_zero] at h
    exact h.trans (hclose n)
  have hz : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hnormconv : Tendsto (fun n => eLpNorm (φ n - u) 6 (volume.restrict (ball x₀ R)))
      atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
        (fun _ => zero_le) hLpbound
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (6 : ℝ≥0∞) ≠ 0)
    (fun n => (hφ n).continuous.aestronglyMeasurable) hu.memLp.aestronglyMeasurable hnormconv
  obtain ⟨ns, _, hns⟩ := hmeasure.exists_seq_tendsto_ae
  exact holder_half_of_smooth_approx hR huc (fun n => φ (ns n)) (fun n => hφ (ns n))
    N.toReal ENNReal.toReal_nonneg (fun n => hgrad (ns n)) hns

#print axioms holder_half_of_smooth_approx
#print axioms holder_half_of_continuous_memW1Six_compact

end Yamabe3.Analysis.GreenRegularPart
