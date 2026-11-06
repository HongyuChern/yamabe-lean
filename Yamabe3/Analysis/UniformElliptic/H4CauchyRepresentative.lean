import Yamabe3.Analysis.UniformElliptic.ThreeDimensionalH4Jets
import Yamabe3.Analysis.UniformElliptic.LocalJetProducts
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Embedding.MorreyHigherOrder

/-!
# The same pointwise limit has its genuine C2 representative

An actual H4-Cauchy sequence on a precompact region has uniformly Cauchy
two-jets on each compact subset. A single fixed geometric cutoff produces
globally smooth functions to which the proved uniform-derivative limit
theorem applies. The resulting C2 function is identified, on actual local
germs, with the already specified pointwise limit of the original sequence.

No extra smooth representative or derivative data are supplied as fields.
Every local H4 profile is finite because the original functions are smooth
on a neighborhood of the closure. This is the representative-consistency
step for completing a weighted H2-to-H4 inverse, not that full completion.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.EuclideanMorrey

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Local smoothness on a neighborhood of the actual compact integration
closure rules out the spurious value `toReal infinity = 0`. -/
theorem derivativeProfile_ne_top_of_local_smooth
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O) (k : ℕ) :
    derivativeProfile 2 V k u ≠ ⊤ := by
  obtain ⟨v, hv, _, hve⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have he : derivativeProfile 2 V k v = derivativeProfile 2 V k u :=
    derivativeProfile_eq_of_local_germs hV.measurableSet
      (fun x hx => hve x (subset_closure hx)) 2 k
  rw [← he]
  exact derivativeProfile_ne_top_on_precompact hVc k hv

/-- The given pointwise limit, rather than a separately chosen function,
is C2 at every point of K. Its actual derivatives are the limits of the
derivatives of the same sequence. No regularity at removed poles is used. -/
theorem contDiffAt_two_of_local_h4_cauchy_of_pointwise_limit
    {K V O : Set E3} (hK : IsCompact K) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hO : IsOpen O)
    (hVO : closure V ⊆ O) (hKV : K ⊆ V)
    (u : ℕ → E3 → ℝ) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) O)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n m : ℕ, N ≤ n → N ≤ m →
        (derivativeProfile 2 V 4 (fun x => u n x - u m x)).toReal ≤ ε)
    (U : E3 → ℝ)
    (hpoint : ∀ x ∈ O, Tendsto (fun n => u n x) atTop (𝓝 (U x))) :
    (∀ n m : ℕ, derivativeProfile 2 V 4 (fun x => u n x - u m x) ≠ ⊤) ∧
    ∀ x ∈ K, ContDiffAt ℝ 2 U x ∧
      ∀ j ≤ 2, Tendsto (fun n => iteratedFDeriv ℝ j (u n) x)
        atTop (𝓝 (iteratedFDeriv ℝ j U x)) := by
  have hfinite (n m : ℕ) :
      derivativeProfile 2 V 4 (fun x => u n x - u m x) ≠ ⊤ :=
    derivativeProfile_ne_top_of_local_smooth hV hVc hO hVO ((hu n).sub (hu m)) 4
  have hnatle (j : ℕ) : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨η, hη, hηc, _, hηone, hηV⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff (hK.cthickening (r := δ)) hV hδV
  obtain ⟨C, hC, hjets⟩ := exists_local_h4_sup_two_jet_bound_on_compact
    hηc hV hVc hO hVO hηV
  let A : ℝ := C * (derivativeProfile 2 V 4 η).toReal
  have hA : 0 ≤ A := mul_nonneg hC.le ENNReal.toReal_nonneg
  have hηjets (j : ℕ) (hj : j ≤ 2) (x : E3) (hx : x ∈ tsupport η) :
      ‖iteratedFDeriv ℝ j η x‖ ≤ A := hjets hη.contDiffOn j hj x hx
  let B : ℝ := max 1 (4 * A * C)
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let v : ℕ → E3 → ℝ := fun n x => η x * u n x
  have hv (n : ℕ) : ContDiff ℝ ∞ (v n) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ O
    · exact hη.contDiffAt.mul ((hu n).contDiffAt (hO.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h =>
        hx (hVO (subset_closure (hηV h))))
      filter_upwards [hzero] with y hy
      change η y * u n y = 0
      change η y = 0 at hy
      rw [hy, zero_mul]
  have hdiff (n m : ℕ) (j : ℕ) (hj : j ≤ 2) (x : E3) :
      ‖iteratedFDeriv ℝ j (v n) x - iteratedFDeriv ℝ j (v m) x‖ ≤
        B * (derivativeProfile 2 V 4 (fun y => u n y - u m y)).toReal := by
    rw [← iteratedFDeriv_sub_apply ((hv n).contDiffAt.of_le (hnatle j))
      ((hv m).contDiffAt.of_le (hnatle j))]
    have he : v n - v m = (fun y => η y * (u n y - u m y)) := by
      funext y
      change η y * u n y - η y * u m y = η y * (u n y - u m y)
      ring
    rw [he]
    by_cases hx : x ∈ tsupport η
    · have hxO : x ∈ O := hVO (subset_closure (hηV hx))
      have huAt := ((hu n).sub (hu m)).contDiffAt (hO.mem_nhds hxO)
      have hlocal := norm_iteratedFDeriv_mul_le_of_local_jets
        (hη.contDiffAt.of_le (hnatle 2))
        (huAt.of_le (hnatle 2)) hA
        (mul_nonneg hC.le ENNReal.toReal_nonneg)
        (fun i hi => hηjets i hi x hx)
        (fun i hi => hjets ((hu n).sub (hu m)) i hi x hx) hj
      apply hlocal.trans
      calc
        _ = (4 * A * C) *
            (derivativeProfile 2 V 4 (fun y => u n y - u m y)).toReal := by norm_num; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg
    · have hezero : (fun y => η y * (u n y - u m y)) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change η y = 0 at hy
        rw [hy, zero_mul]
      rw [(hezero.iteratedFDeriv ℝ j).self_of_nhds]
      simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
      exact mul_nonneg hB.le ENNReal.toReal_nonneg
  have huc (j : ℕ) (hj : j ≤ 2) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → ∀ x : E3,
        ‖iteratedFDeriv ℝ j (v n) x - iteratedFDeriv ℝ j (v m) x‖ ≤ ε := by
    obtain ⟨N, hN⟩ := hCauchy (ε / B) (div_pos hε hB)
    refine ⟨N, fun n m hn hm x => (hdiff n m j hj x).trans ?_⟩
    calc
      _ ≤ B * (ε / B) := mul_le_mul_of_nonneg_left (hN n m hn hm) hB.le
      _ = ε := mul_div_cancel₀ ε hB.ne'
  have huc0 : ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → ∀ x : E3,
      ‖v n x - v m x‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := huc 0 (by norm_num) ε hε
    refine ⟨N, ?_⟩
    intro n m hn hm x
    have hb := hN n m hn hm x
    rw [← iteratedFDeriv_sub_apply ((hv n).contDiffAt.of_le (hnatle 0))
      ((hv m).contDiffAt.of_le (hnatle 0)), norm_iteratedFDeriv_zero] at hb
    exact hb
  let W := cauchyLimitFun v huc0
  have hlimit := iteratedFDeriv_cauchyLimitFun_eq 2 hv huc0 huc
  have hW : ContDiff ℝ 2 W := hlimit.1
  have hWpoint (x : E3) (hx : x ∈ O) : W x = η x * U x := by
    apply tendsto_nhds_unique (cauchyLimitFun_tendsto huc0 x)
    exact tendsto_const_nhds.mul (hpoint x hx)
  have hηgerm (x : E3) (hx : x ∈ K) : η =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ K hx)] with y hy
    exact hηone y (Metric.thickening_subset_cthickening δ K hy)
  have hWgerm (x : E3) (hx : x ∈ K) : W =ᶠ[𝓝 x] U := by
    filter_upwards [hηgerm x hx, hO.mem_nhds (hVO (subset_closure (hKV hx)))] with y hηy hy
    rw [hWpoint y hy, hηy, one_mul]
  refine ⟨hfinite, ?_⟩
  intro x hx
  refine ⟨hW.contDiffAt.congr_of_eventuallyEq (hWgerm x hx).symm, ?_⟩
  intro j hj
  have hvg (n : ℕ) : v n =ᶠ[𝓝 x] u n := by
    filter_upwards [hηgerm x hx] with y hy
    change η y * u n y = u n y
    rw [hy, one_mul]
  have h := hlimit.2 j hj x
  have he (n : ℕ) : iteratedFDeriv ℝ j (v n) x = iteratedFDeriv ℝ j (u n) x :=
    ((hvg n).iteratedFDeriv ℝ j).self_of_nhds
  have hwe : iteratedFDeriv ℝ j W x = iteratedFDeriv ℝ j U x :=
    ((hWgerm x hx).iteratedFDeriv ℝ j).self_of_nhds
  change Tendsto (fun n => iteratedFDeriv ℝ j (v n) x) atTop
    (𝓝 (iteratedFDeriv ℝ j W x)) at h
  simpa only [he, hwe] using h

#print axioms derivativeProfile_ne_top_of_local_smooth
#print axioms contDiffAt_two_of_local_h4_cauchy_of_pointwise_limit

end Yamabe3.Analysis.UniformElliptic
