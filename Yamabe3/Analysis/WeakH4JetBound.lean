import Yamabe3.Analysis.WeakH4LocalRepresentative
import Yamabe3.Analysis.CompactWeakH4JetRepresentative
import Yamabe3.Analysis.WeakFlatH4Estimate

/-! Quantitative H4 control of the actual continuous representative.
The constant precedes the weak function and no pointwise value is chosen
from an arbitrary L2 representative. Smooth approximation and full-norm
convergence transfer the existing genuine three-dimensional embedding. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_weak_H4_two_jet_bound_on_compact {K V : Set E}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u F : E → ℝ), MemWkp 4 2 u V → ContinuousOn F V →
      F =ᵐ[volume.restrict V] u → ∀ j ≤ 2, ∀ x ∈ K,
        ENNReal.ofReal ‖iteratedFDeriv ℝ j F x‖ ≤ C*iteratedWeakSobolevNorm 4 2 u V := by
  obtain ⟨W,hW,hKW,hWV,hWc⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨C,hC,hb⟩ := exists_h4_sup_two_jet_bound_on_compact hK hW hWc hKW
  refine ⟨ENNReal.ofReal C,ENNReal.ofReal_ne_top,?_⟩
  intro u F hu hF hFu j hj x hx
  obtain ⟨v,U,hU,hWU,hvc,hv,hvu⟩ := exists_compact_sobolev_extension_near_compact
    (locally_of_memWkp hV hu) hWc hWV
  obtain ⟨G,φ,hG,hGv,hφ,herr,hpoint⟩ := exists_compact_weak_H4_C2_jet_representative hv hvc
  have hvuW : v =ᵐ[volume.restrict W] u := by
    filter_upwards [ae_restrict_mem hW.measurableSet] with y hy
    exact hvu (hWU (subset_closure hy))
  have hFuW : F =ᵐ[volume.restrict W] u :=
    ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hWV) hFu
  have hGvW : G =ᵐ[volume.restrict W] v := ae_restrict_of_ae hGv
  have hGF : EqOn G F W := Measure.eqOn_open_of_ae_eq
    (hGvW.trans (hvuW.trans hFuW.symm)) hW
    hG.continuous.continuousOn (hF.mono (subset_closure.trans hWV))
  have hφW (n : ℕ) := (hφ n).2.2.mono_set (by norm_num : (1:ℝ≥0∞) ≤ 2) hW (subset_univ W)
  have hvW := hv.mono_set (by norm_num : (1:ℝ≥0∞) ≤ 2) hW (subset_univ W)
  have hdiff : Tendsto (fun n => iteratedWeakSobolevNorm 4 2 (fun y => φ n y-v y) W) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto (fun _ => zero_le)
      (sobolev_approx_error_on_subset hW (le_refl 4) (fun n => (hφ n).2.2) hv herr)
  have hn := sobolevNorm_tendsto_of_difference hW hφW hvW hdiff
  have hbnd (n : ℕ) : ENNReal.ofReal ‖iteratedFDeriv ℝ j (φ n) x‖ ≤ ENNReal.ofReal C*iteratedWeakSobolevNorm 4 2 (φ n) W := by
    have h := hb (hφ n).1 j hj x hx
    have hf := (wkpNorm_lt_top_of_memWkp (hφW n)).ne
    have hp := local_profile_le_actual_weak_norm hW hWc isOpen_univ (subset_univ _) (hφ n).1.contDiffOn 4
    have hr := h.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hf hp) hC.le)
    have hh := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_mul hC.le,ENNReal.ofReal_toReal hf] at hh
    exact hh
  have hlim := le_of_tendsto_of_tendsto'
    (ENNReal.continuous_ofReal.tendsto _ |>.comp (hpoint x j hj).norm)
    (ENNReal.Tendsto.const_mul hn (Or.inr ENNReal.ofReal_ne_top)) hbnd
  have hge : G =ᶠ[𝓝 x] F := by
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact hGF hy
  rw [(hge.iteratedFDeriv ℝ j).self_of_nhds,wkpNorm_congr_ae (k := 4) (by norm_num) hW hvuW] at hlim
  exact hlim.trans (mul_le_mul le_rfl
    (wkpNorm_mono_set (by norm_num) hW (subset_closure.trans hWV) hu) zero_le zero_le)

#print axioms exists_weak_H4_two_jet_bound_on_compact
end Yamabe3.Analysis.UniformElliptic
