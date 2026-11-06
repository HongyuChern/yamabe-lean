import Yamabe3.Analysis.UniformElliptic.ThreeDimensionalH2Embedding
import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.ProfileCalculus

/-!
# Quantitative H4 control of actual two-jets in dimension three

The inherited quantitative H2-to-C0 estimate is applied to actual scalar
coordinate derivatives, and the genuine multilinear derivative norm is
recovered by Euclidean basis expansion. Thus two pointwise derivatives
consume four L2 derivatives, with one constant preceding the function.
This is the embedding compatible with an H2-source/H4-solution scheme.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_h4_sup_two_jet_bound_on_compact {K V : Set E3}
    (hK : IsCompact K) (hV : IsOpen V) (hVc : IsCompact (closure V)) (hKV : K ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : E3 → ℝ}, ContDiff ℝ ∞ u →
      ∀ n ≤ 2, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n u x‖ ≤ C * (derivativeProfile 2 V 4 u).toReal := by
  obtain ⟨C, hC, hsup⟩ := exists_h2_sup_bound_on_compact hK hV hVc hKV
  have hfirst {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (x : E3) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ 1 f x‖ ≤ (3 * C) * (derivativeProfile 2 V 3 f).toReal := by
    have hfinite := derivativeProfile_ne_top_on_precompact hVc 3 hf
    calc
      _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ 0 (partialDeriv i f) x‖ :=
        norm_iteratedFDeriv_succ_le_sum_partial hf 0 x
      _ ≤ ∑ _i : Fin 3, C * (derivativeProfile 2 V 3 f).toReal := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_iteratedFDeriv_zero]
        exact (hsup (contDiff_partial hf i) x hx).trans
          (mul_le_mul_of_nonneg_left
            (ENNReal.toReal_mono hfinite (derivativeProfile_partial_le 2 i hf)) hC.le)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  refine ⟨9 * C, mul_pos (by norm_num) hC, ?_⟩
  intro u hu n hn x hx
  have hfinite := derivativeProfile_ne_top_on_precompact hVc 4 hu
  have hPnonneg : 0 ≤ (derivativeProfile 2 V 4 u).toReal := ENNReal.toReal_nonneg
  interval_cases n
  · rw [norm_iteratedFDeriv_zero]
    have hbase := (hsup hu x hx).trans
      (mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono hfinite (derivativeProfile_mono_order (by norm_num : 2 ≤ 4) u)) hC.le)
    exact hbase.trans (by nlinarith only [mul_nonneg hC.le hPnonneg])
  · have hbase := (hfirst hu x hx).trans
      (mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono hfinite (derivativeProfile_mono_order (by norm_num : 3 ≤ 4) u))
        (by positivity : 0 ≤ 3 * C))
    exact hbase.trans (by nlinarith only [mul_nonneg hC.le hPnonneg])
  · calc
      _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ 1 (partialDeriv i u) x‖ :=
        norm_iteratedFDeriv_succ_le_sum_partial hu 1 x
      _ ≤ ∑ _i : Fin 3, (3 * C) * (derivativeProfile 2 V 4 u).toReal := by
        apply Finset.sum_le_sum
        intro i _
        exact (hfirst (contDiff_partial hu i) x hx).trans
          (mul_le_mul_of_nonneg_left
            (ENNReal.toReal_mono hfinite (derivativeProfile_partial_le 3 i hu))
            (by positivity : 0 ≤ 3 * C))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring

/-- The H2 value embedding for an actual function smooth only on a
neighborhood of the compact integration region. -/
theorem exists_local_h2_sup_bound_on_compact {K V O : Set E3}
    (hK : IsCompact K) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O) (hKV : K ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : E3 → ℝ}, ContDiffOn ℝ ∞ u O →
      ∀ x ∈ K, ‖u x‖ ≤ C * (derivativeProfile 2 V 2 u).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_h2_sup_bound_on_compact hK hV hVc hKV
  refine ⟨C, hC, ?_⟩
  intro u hu x hx
  obtain ⟨v, hv, _, hve⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have hvg (y : E3) (hy : y ∈ V) : v =ᶠ[𝓝 y] u := hve y (subset_closure hy)
  have h := hbound hv x hx
  rw [derivativeProfile_eq_of_local_germs hV.measurableSet hvg 2 2,
    (hvg x (hKV hx)).self_of_nhds] at h
  exact h

/-- The two-jet embedding for the same punctured-domain representative.
The finite profile and the derivatives are transferred through actual
local germs; no extension value at the pole is imposed on u. -/
theorem exists_local_h4_sup_two_jet_bound_on_compact {K V O : Set E3}
    (hK : IsCompact K) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O) (hKV : K ⊆ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : E3 → ℝ}, ContDiffOn ℝ ∞ u O →
      ∀ n ≤ 2, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n u x‖ ≤ C * (derivativeProfile 2 V 4 u).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_h4_sup_two_jet_bound_on_compact hK hV hVc hKV
  refine ⟨C, hC, ?_⟩
  intro u hu n hn x hx
  obtain ⟨v, hv, _, hve⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have hvg (y : E3) (hy : y ∈ V) : v =ᶠ[𝓝 y] u := hve y (subset_closure hy)
  have h := hbound hv n hn x hx
  rw [derivativeProfile_eq_of_local_germs hV.measurableSet hvg 2 4,
    ((hvg x (hKV hx)).iteratedFDeriv ℝ n).self_of_nhds] at h
  exact h

#print axioms exists_local_h2_sup_bound_on_compact
#print axioms exists_local_h4_sup_two_jet_bound_on_compact

#print axioms exists_h4_sup_two_jet_bound_on_compact

end Yamabe3.Analysis.UniformElliptic
