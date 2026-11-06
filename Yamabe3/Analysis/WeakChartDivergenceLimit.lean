import Yamabe3.Analysis.WeightedChartOperatorContinuity
import Yamabe3.Analysis.LocalSmoothWeakDivergence

/-! Transfer of a proved smooth coordinate operator identity to the same
compact H2 input. Both sides converge through their actual H2-to-L2 bounds.
The smooth identity is an intermediate interface, discharged for the native
metric in the downstream geometric specialization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem weak_chart_divergence_of_smooth_identity_compact
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOs : closure O⊆e.source) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (heW : e '' closure O⊆W)
    (a b : E → Matrix (Fin 3) (Fin 3) ℝ)
    (ha : ∀ i j,ContDiff ℝ ∞ (fun x => a x i j))
    (hb : ∀ i j,ContDiff ℝ ∞ (fun x => b x i j))
    (σ : E → ℝ) (hσ : ContDiffOn ℝ ∞ σ e.source)
    (hsmooth : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ x∈O,principalSource b (φ∘e) x=σ x*principalSource a φ (e x))
    {u : E → ℝ} (hu : MemWkp 2 2 u univ) (huc : HasCompactSupport u) :
    MemWkp 2 2 (u∘e) O ∧
      weakDivergenceSource O b (u∘e) =ᵐ[volume.restrict O]
        fun x => σ x*weakDivergenceSource W a u (e x) := by
  obtain ⟨φ,hφ,herr,-⟩ := exists_smooth_sobolev_sequence 2 hu huc
  have huW := hu.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hW (subset_univ _)
  have hφW (n : ℕ) := (hφ n).2.2.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hW (subset_univ _)
  obtain ⟨P,hP,hp⟩ := exists_euclidean_chart_source_bound 2 e he hei hO hOc hOs hW heW
  have huO := (hp u huW).1
  have hφO (n : ℕ) := (hp (φ n) (hφW n)).1
  obtain ⟨D,hD,hd⟩ := exists_weakDivergenceSource_difference_bound hO hOc b hb
  obtain ⟨K,hK,hk⟩ := exists_weakDivergenceSource_bound hO hOc b hb
  obtain ⟨R,hR,hrm,hr⟩ := exists_weighted_chart_operator_difference_bound
    e he hei hO hOc hOs hW hWc heW a ha σ hσ
  let L : E → ℝ := weakDivergenceSource O b (u∘e)
  let T : E → ℝ := fun x => σ x*weakDivergenceSource W a u (e x)
  let Ln : ℕ → E → ℝ := fun n => weakDivergenceSource O b (φ n∘e)
  let Tn : ℕ → E → ℝ := fun n x => σ x*weakDivergenceSource W a (φ n) (e x)
  have hL : MemLp L 2 (volume.restrict O) := (hk _ huO).1.memLp
  have hT : MemLp T 2 (volume.restrict O) := (hrm u huW).memLp
  have hLn (n : ℕ) : MemLp (Ln n) 2 (volume.restrict O) := (hk _ (hφO n)).1.memLp
  have hEq (n : ℕ) : Ln n =ᵐ[volume.restrict O] Tn n := by
    have hc : ContDiffOn ℝ ∞ (φ n∘e) e.source :=
      (hφ n).1.comp_contDiffOn he.contDiffOn
    have hl := (weakDivergenceSource_smoothOn_ae hO hOc e.open_source hOs b hb hc).2
    have hh := weakDivergenceSource_smooth_ae hW hWc a ha (hφ n).1 (hφW n)
    have ht := euclidean_chart_comp_congr_ae_restrict e he hei hO hW
      (subset_closure.trans hOs) (fun x hx => heW (mem_image_of_mem e (subset_closure hx))) hh
    filter_upwards [hl,ht,ae_restrict_mem hO.measurableSet] with x hx hy hxo
    exact hx.trans ((hsmooth (φ n) (hφ n).1 (hφ n).2.1 x hxo).trans (congrArg (σ x*·) hy.symm))
  have hErr (n : ℕ) : iteratedWeakSobolevNorm 2 2 (fun x => φ n x-u x) W ≤ sobolevApproxError n :=
    (wkpNorm_mono_set (by norm_num) hW (subset_univ _)
      (MemWkp.sub (by norm_num) isOpen_univ (hφ n).2.2 hu)).trans (herr n)
  have hLeft (n : ℕ) : eLpNorm (fun x => Ln n x-L x) 2 (volume.restrict O) ≤
      (D*P)*sobolevApproxError n := by
    have h1 := hd (φ n∘e) (u∘e) (hφO n) huO
    have h2 := (hp (fun x => φ n x-u x) (MemWkp.sub (by norm_num) hW (hφW n) huW)).2
    simp only [wkpNorm_zero] at h1
    exact h1.trans ((mul_le_mul le_rfl h2 zero_le zero_le).trans
      (by simpa only [mul_assoc] using mul_le_mul (le_refl (D*P)) (hErr n) zero_le zero_le))
  have hRight (n : ℕ) : eLpNorm (fun x => Tn n x-T x) 2 (volume.restrict O) ≤
      R*sobolevApproxError n := by
    have hh := hr (φ n) u (hφW n) huW
    simp only [wkpNorm_zero] at hh
    exact hh.trans (mul_le_mul le_rfl (hErr n) zero_le zero_le)
  have htL : Tendsto (fun n => eLpNorm (fun x => Ln n x-L x) 2 (volume.restrict O)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using (ENNReal.Tendsto.const_mul sobolevApproxError_tendsto (Or.inr (ENNReal.mul_ne_top hD hP)))) (fun _ => zero_le) hLeft
  have htT : Tendsto (fun n => eLpNorm (fun x => Ln n x-T x) 2 (volume.restrict O)) atTop (𝓝 0) := by
    have ht := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using (ENNReal.Tendsto.const_mul sobolevApproxError_tendsto (Or.inr hR))) (fun _ => zero_le) hRight
    apply ht.congr'
    filter_upwards [] with n
    exact (eLpNorm_congr_ae ((hEq n).sub (Filter.EventuallyEq.refl _ _))).symm
  have hlp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Ln hLn L hL).mpr htL
  have htp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Ln hLn T hT).mpr htT
  exact ⟨huO,(MemLp.toLp_eq_toLp_iff hL hT).mp (tendsto_nhds_unique hlp htp)⟩

#print axioms weak_chart_divergence_of_smooth_identity_compact
end Yamabe3.Analysis.UniformElliptic
