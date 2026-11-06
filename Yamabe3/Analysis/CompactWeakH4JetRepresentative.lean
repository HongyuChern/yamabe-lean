import Yamabe3.Analysis.SobolevApproximationSequence
import Yamabe3.Analysis.UniformElliptic.H4CanonicalLimit
import Yamabe3.Analysis.UniformElliptic.LocalProfileWeakNormComparison

/-! Genuine C2 representatives of compact weak H4 functions in dimension
three, obtained from smooth approximation of the very same L2 class. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_compact_weak_H4_C2_jet_representative {u : E → ℝ}
    (hu : MemWkp 4 2 u univ) (huc : HasCompactSupport u) :
    ∃ (F : E → ℝ) (φ : ℕ → E → ℝ), ContDiff ℝ 2 F ∧ F =ᵐ[volume] u ∧
      (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧ MemWkp 4 2 (φ n) univ) ∧
      (∀ n, iteratedWeakSobolevNorm 4 2 (fun x => φ n x-u x) univ ≤ sobolevApproxError n) ∧
      (∀ x : E, ∀ j ≤ 2, Tendsto (fun n => iteratedFDeriv ℝ j (φ n) x) atTop
        (𝓝 (iteratedFDeriv ℝ j F x))) := by
  obtain ⟨φ,hφ,hb,hn⟩ := exists_smooth_sobolev_sequence 4 hu huc
  have hdiff (n m : ℕ) : iteratedWeakSobolevNorm 4 2 (fun x => φ n x-φ m x) univ ≤
      sobolevApproxError n+sobolevApproxError m := by
    have he : (fun x => φ n x-φ m x) = (fun x => (φ n x-u x)-(φ m x-u x)) := by funext x; ring
    rw [he]
    exact (weak_sobolev_norm_sub_le isOpen_univ 4
      (MemWkp.sub (by norm_num) isOpen_univ (hφ n).2.2 hu)
      (MemWkp.sub (by norm_num) isOpen_univ (hφ m).2.2 hu)).trans (add_le_add (hb n) (hb m))
  have hCauchy : ∀ V : Set E, IsOpen V → IsCompact (closure V) → closure V ⊆ univ →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        (derivativeProfile 2 V 4 (fun x => φ n x-φ m x)).toReal ≤ ε := by
    intro V hV hVc hVU ε hε
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N,?_⟩
    intro n m hn hm
    have hh : derivativeProfile 2 V 4 (fun x => φ n x-φ m x) ≤ sobolevApproxError n+sobolevApproxError m :=
      (local_profile_le_actual_weak_norm hV hVc isOpen_univ hVU
        ((hφ n).1.sub (hφ m).1).contDiffOn 4).trans
        ((wkpNorm_mono_set (by norm_num) hV (subset_univ V)
          (MemWkp.sub (by norm_num) isOpen_univ (hφ n).2.2 (hφ m).2.2)).trans (hdiff n m))
    have hfinite : sobolevApproxError n+sobolevApproxError m ≠ ⊤ := by
      unfold sobolevApproxError
      finiteness
    have h := ENNReal.toReal_mono hfinite hh
    simp only [sobolevApproxError,ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (1/2:ℝ)^n),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (1/2:ℝ)^m)] at h
    exact h.trans (by linarith [hN n hn,hN m hm])
  have hL2 : Tendsto (fun n => eLpNorm (fun x => φ n x-u x) 2 (volume.restrict univ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sobolevApproxError_tendsto (fun _ => zero_le)
    intro n
    change eLpNorm (fun x => φ n x-u x) 2 (volume.restrict univ) ≤ sobolevApproxError n
    rw [← wkpNorm_zero]
    exact (wkpNorm_mono_order (by norm_num : 0 ≤ 4) _ univ).trans (hb n)
  obtain ⟨F,hF,hFu,hpoint,-⟩ := exists_same_c2_canonical_limit_of_locally_h4_cauchy volume isOpen_univ
    φ (fun n => (hφ n).1.contDiffOn) hCauchy u hu.memLp.aestronglyMeasurable hL2
  exact ⟨F,φ,contDiffOn_univ.mp hF,by simpa only [Measure.restrict_univ] using hFu,
    hφ,hb,fun x => (hpoint x (mem_univ x)).2⟩

#print axioms exists_compact_weak_H4_C2_jet_representative
end Yamabe3.Analysis.UniformElliptic
