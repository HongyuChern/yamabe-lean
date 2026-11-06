import Yamabe3.Analysis.UniformElliptic.H4CanonicalLimit
import Yamabe3.Analysis.UniformElliptic.WeakSobolevCauchyLimit

/-!
# Completing the actual local Hk profile in the same weak Sobolev class

Local smooth functions need not vanish on the boundary of the integration
region. We extend them near its compact closure, use weak derivatives on
the full Euclidean space, and then restrict those same derivatives back.
This gives a coordinate weak-jet norm bound by the actual classical
derivative profile, with constant one for each coordinate tuple.

The bound makes every weak jet of a classical-profile Cauchy sequence
Cauchy in L2. The already proved closed weak-derivative graph constructs
its Hk limit. A pointwise limit of the same sequence is then identified
with that Hk function and inherits its actual weak jets. No classical
derivative of order above the regularity already obtained is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.Euclidean

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A local smooth function belongs to every finite weak Sobolev class
on a precompact open subregion, without a zero boundary condition. -/
theorem memWk2_of_local_smooth
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O) (k : ℕ) :
    MemWkp k 2 u V := by
  obtain ⟨v, hv, hvc, hve⟩ :=
    exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have hvW : MemWkp k 2 v univ := MemWkp_of_smooth_compactSupport
    isOpen_univ hv hvc (subset_univ _) (by norm_num) k
  have hae : v =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact (hve x (subset_closure hx)).self_of_nhds
  exact (MemWkp_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV hae).mp
    (hvW.mono_set (by norm_num) hV (subset_univ _))

/-- Each actual weak coordinate jet is bounded by the same local
classical profile. The extension disappears from the final bound. -/
theorem eLpNorm_weak_jet_le_local_profile
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    {u : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O)
    {j k : ℕ} (hj : j ≤ k) (β : Fin j → Fin 3) :
    eLpNorm (iterWeakPartial 2 j β u V) 2 (volume.restrict V) ≤
      derivativeProfile 2 V k u := by
  obtain ⟨v, hv, hvc, hve⟩ :=
    exists_smooth_compact_extension_near_compact hO hVc hVO hu
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hvW : MemWkp j 2 v univ := MemWkp_of_smooth_compactSupport
    isOpen_univ hv hvc (subset_univ _) hp j
  have hae : v =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact (hve x (subset_closure hx)).self_of_nhds
  have hg : iterWeakPartial 2 j β v univ =ᵐ[volume]
      iterClassicalPartial j β v := by
    simpa only [Measure.restrict_univ] using
      iterWeakPartial_smooth_ae_eq_iterClassicalPartial hp isOpen_univ j β
        hv hvc (subset_univ _)
  have hl : iterWeakPartial 2 j β v univ =ᵐ[volume.restrict V]
      iterWeakPartial 2 j β v V :=
    iterWeakPartial_mono_set_ae hp hV (subset_univ _) β hvW
  have hc : iterWeakPartial 2 j β v V =ᵐ[volume.restrict V]
      iterWeakPartial 2 j β u V := iterWeakPartial_ae_congr hp hV j β hae
  have hweak : iterWeakPartial 2 j β u V =ᵐ[volume.restrict V]
      iterClassicalPartial j β v := hc.symm.trans (hl.symm.trans (ae_restrict_of_ae hg))
  rw [eLpNorm_congr_ae hweak]
  calc
    _ ≤ eLpNorm (fun x => ‖iteratedFDeriv ℝ j v x‖) 2 (volume.restrict V) := by
      apply eLpNorm_mono_ae
      exact Eventually.of_forall fun x => by
        have h := norm_iteratedFDeriv_iterClassicalPartial_le j 0 β hv x
        rw [norm_iteratedFDeriv_zero, Nat.zero_add] at h
        simpa only [norm_norm] using h
    _ ≤ derivativeProfile 2 V k v := by
      unfold derivativeProfile
      exact Finset.single_le_sum
        (f := fun i => eLpNorm (fun x => ‖iteratedFDeriv ℝ i v x‖) 2 (volume.restrict V))
        (fun _ _ => zero_le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    _ = derivativeProfile 2 V k u :=
      derivativeProfile_eq_of_local_germs hV.measurableSet
        (fun x hx => hve x (subset_closure hx)) 2 k

/-- Subtraction is performed in the actual weak derivative class before
applying the classical-profile estimate to the same difference. -/
private theorem iterWeakPartial_sub_ae_local
    {V : Set E3} (hV : IsOpen V) {j : ℕ} (β : Fin j → Fin 3)
    {u v : E3 → ℝ} (hu : MemWkp j 2 u V) (hv : MemWkp j 2 v V) :
    iterWeakPartial 2 j β (fun x => u x - v x) V =ᵐ[volume.restrict V]
      (fun x => iterWeakPartial 2 j β u V x - iterWeakPartial 2 j β v V x) := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hn : iterWeakPartial 2 j β (fun x => -v x) V =ᵐ[volume.restrict V]
      (fun x => -iterWeakPartial 2 j β v V x) := by
    simpa only [neg_one_mul] using iterWeakPartial_const_smul_ae hp hV β hv (-1 : ℝ)
  have ha := iterWeakPartial_add_ae hp hV β hu (MemWkp.neg hp hV hv)
  have hs : (fun x => u x + -v x) = (fun x => u x - v x) := by
    funext x
    exact (sub_eq_add_neg _ _).symm
  rw [hs] at ha
  refine ha.trans ?_
  filter_upwards [hn] with x hx
  rw [hx, sub_eq_add_neg]

theorem eLpNorm_weak_jet_sub_le_local_profile
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O)
    {u v : E3 → ℝ} (hu : ContDiffOn ℝ ∞ u O) (hv : ContDiffOn ℝ ∞ v O)
    {j k : ℕ} (hj : j ≤ k) (β : Fin j → Fin 3) :
    eLpNorm (fun x => iterWeakPartial 2 j β u V x - iterWeakPartial 2 j β v V x)
      2 (volume.restrict V) ≤ derivativeProfile 2 V k (fun x => u x - v x) := by
  rw [← eLpNorm_congr_ae (iterWeakPartial_sub_ae_local hV β
    (memWk2_of_local_smooth hV hVc hO hVO hu j)
    (memWk2_of_local_smooth hV hVc hO hVO hv j))]
  exact eLpNorm_weak_jet_le_local_profile hV hVc hO hVO (hu.sub hv) hj β

/-- The two-index real-profile Cauchy condition is an actual ENNReal
limit because all profiles were proved finite on the compact closure. -/
theorem local_profile_cauchy_tendsto_zero
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O) (k : ℕ)
    (u : ℕ → E3 → ℝ) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) O)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      (derivativeProfile 2 V k (fun x => u n x - u m x)).toReal ≤ ε) :
    Tendsto (fun nm : ℕ × ℕ => derivativeProfile 2 V k
      (fun x => u nm.1 x - u nm.2 x)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  by_cases hεtop : ε = ⊤
  · refine ⟨(0, 0), ?_⟩
    intro nm _
    rw [hεtop]
    exact le_top
  have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨N, hN⟩ := hCauchy ε.toReal hεreal
  refine ⟨(N, N), ?_⟩
  intro nm hnm
  exact (ENNReal.toReal_le_toReal
    (derivativeProfile_ne_top_of_local_smooth hV hVc hO hVO
      ((hu nm.1).sub (hu nm.2)) k) hεtop).mp
        (hN nm.1 nm.2 hnm.1 hnm.2)

/-- The fixed pointwise limit is in the actual weak Hk class, and all
weak jets of the original sequence converge to its own weak jets. -/
theorem memWk2_same_pointwise_limit_of_local_profile_cauchy
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O) (k : ℕ)
    (u : ℕ → E3 → ℝ) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) O)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      (derivativeProfile 2 V k (fun x => u n x - u m x)).toReal ≤ ε)
    (U : E3 → ℝ)
    (hpoint : ∀ x ∈ V, Tendsto (fun n => u n x) atTop (𝓝 (U x))) :
    MemWkp k 2 U V ∧ ∀ (j : ℕ) (β : Fin j → Fin 3), j ≤ k →
      Tendsto (fun n => eLpNorm
        (fun x => iterWeakPartial 2 j β (u n) V x - iterWeakPartial 2 j β U V x)
          2 (volume.restrict V)) atTop (𝓝 0) := by
  have huW (n : ℕ) : MemWkp k 2 (u n) V :=
    memWk2_of_local_smooth hV hVc hO hVO (hu n) k
  have hprofile := local_profile_cauchy_tendsto_zero hV hVc hO hVO k u hu hCauchy
  have hweakC (j : ℕ) (β : Fin j → Fin 3) (hj : j ≤ k) :
      Tendsto (fun nm : ℕ × ℕ => eLpNorm
        (fun x => iterWeakPartial 2 j β (u nm.1) V x - iterWeakPartial 2 j β (u nm.2) V x)
          2 (volume.restrict V)) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.mp hprofile ε hε] with nm hnm
    exact (eLpNorm_weak_jet_sub_le_local_profile hV hVc hO hVO
      (hu nm.1) (hu nm.2) hj β).trans hnm
  obtain ⟨W, hW, hjets⟩ := exists_memWk2_limit_of_iterated_weak_cauchy hV k huW hweakC
  have hvalue : Tendsto (fun n => eLpNorm (fun x => u n x - W x) 2 (volume.restrict V))
      atTop (𝓝 0) := by
    simpa only [iterWeakPartial_zero] using hjets 0 ![] (Nat.zero_le k)
  have hae : U =ᵐ[volume.restrict V] W :=
    ae_eq_of_l2_limit_of_pointwise_limit_on_open volume hV
      (fun n => ((hu n).continuousOn).mono (subset_closure.trans hVO))
      hW.memLp.aestronglyMeasurable hvalue hpoint
  refine ⟨(MemWkp_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV hae).mpr hW, ?_⟩
  intro j β hj
  have hjetae := iterWeakPartial_ae_congr (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV j β hae
  apply (hjets j β hj).congr'
  exact Eventually.of_forall fun n => by
    apply eLpNorm_congr_ae
    filter_upwards [hjetae] with x hx
    rw [hx]

/-- Uniform estimates for the actual classical profiles survive in the
same limit's full coordinate weak norm. The displayed finite factor is
explicit (121 for k=4 in dimension three) and is independent of the
sequence, geometric scale and source. -/
theorem memWk2_same_pointwise_limit_with_profile_bound
    {V O : Set E3} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hO : IsOpen O) (hVO : closure V ⊆ O) (k : ℕ)
    (u : ℕ → E3 → ℝ) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) O)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      (derivativeProfile 2 V k (fun x => u n x - u m x)).toReal ≤ ε)
    (U : E3 → ℝ)
    (hpoint : ∀ x ∈ V, Tendsto (fun n => u n x) atTop (𝓝 (U x)))
    (B : ℝ≥0∞) (hB : ∀ n, derivativeProfile 2 V k (u n) ≤ B) :
    MemWkp k 2 U V ∧ iteratedWeakSobolevNorm k 2 U V ≤
      (∑ j ∈ Finset.range (k + 1), (Fintype.card (Fin j → Fin 3) : ℝ≥0∞)) * B := by
  classical
  obtain ⟨hU, hjet⟩ := memWk2_same_pointwise_limit_of_local_profile_cauchy
    hV hVc hO hVO k u hu hCauchy U hpoint
  have hbound (j : ℕ) (β : Fin j → Fin 3) (hj : j ≤ k) :
      eLpNorm (iterWeakPartial 2 j β U V) 2 (volume.restrict V) ≤ B := by
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (iterWeakPartial 2 j β (u n) V) (volume.restrict V) :=
      (iterWeakPartial_memLp_of_memWkp
        ((memWk2_of_local_smooth hV hVc hO hVO (hu n) k).le_of_le hj) β).aestronglyMeasurable
    have hUmeas : AEStronglyMeasurable (iterWeakPartial 2 j β U V) (volume.restrict V) :=
      (iterWeakPartial_memLp_of_memWkp (hU.le_of_le hj) β).aestronglyMeasurable
    have hm := tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) hmeas hUmeas (hjet j β hj)
    obtain ⟨σ, _, hσ⟩ := hm.exists_seq_tendsto_ae
    exact Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun n =>
      (eLpNorm_weak_jet_le_local_profile hV hVc hO hVO (hu (σ n)) hj β).trans (hB (σ n)))
        (fun n => hmeas (σ n)) hσ
  refine ⟨hU, ?_⟩
  rw [wkpNorm_eq_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ ∑ _β : Fin j → Fin 3, B :=
      Finset.sum_le_sum (fun β _ => hbound j β hjk)
    _ = (Fintype.card (Fin j → Fin 3) : ℝ≥0∞) * B := by simp [nsmul_eq_mul]

#print axioms memWk2_of_local_smooth
#print axioms eLpNorm_weak_jet_le_local_profile
#print axioms eLpNorm_weak_jet_sub_le_local_profile
#print axioms local_profile_cauchy_tendsto_zero
#print axioms memWk2_same_pointwise_limit_of_local_profile_cauchy
#print axioms memWk2_same_pointwise_limit_with_profile_bound

end Yamabe3.Analysis.UniformElliptic
