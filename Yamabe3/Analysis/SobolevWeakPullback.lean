import Yamabe3.Analysis.SobolevApproximationSequence

/-! Bounded pullback of the same actual weak Hk input. The proof constructs
all weak derivatives by closedness and identifies the value limit in L2.
No regularity of the pullback is supplied as an assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Full weak Hk continuity of a fixed smooth coordinate map on a
precompact open set, with actual measure domination. Compact support is
required only of the ambient input, not at the coordinate-domain boundary. -/
theorem exists_weak_sobolev_pullback_bound
    (k : ℕ) {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (Φ : E → E) (hΦ : ContDiff ℝ ∞ Φ) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (hmap : (volume.restrict O).map Φ ≤ c • volume) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ,
      MemWkp k 2 u univ → HasCompactSupport u →
      MemWkp k 2 (fun x => u (Φ x)) O ∧
      iteratedWeakSobolevNorm k 2 (fun x => u (Φ x)) O ≤
        C * iteratedWeakSobolevNorm k 2 u univ := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_smooth_sobolev_pullback_bound k hO hOc Φ hΦ c hc hmap
  refine ⟨C, hC, ?_⟩
  intro u hu huc
  obtain ⟨φ, hφ, hb, hnorm⟩ := exists_smooth_sobolev_sequence k hu huc
  let v : ℕ → E → ℝ := fun n x => φ n (Φ x)
  have hv (n : ℕ) : MemWkp k 2 (v n) O :=
    smooth_memWkp_on_precompact k hO hOc ((hφ n).1.comp hΦ)
  have hdiff (n m : ℕ) : iteratedWeakSobolevNorm k 2 (fun x => φ n x - φ m x) univ ≤
      sobolevApproxError n + sobolevApproxError m := by
    have heq : (fun x => φ n x - φ m x) =
        (fun x => (φ n x - u x) - (φ m x - u x)) := by funext x; ring
    rw [heq]
    exact (weak_sobolev_norm_sub_le isOpen_univ k
      (MemWkp.sub (by norm_num) isOpen_univ (hφ n).2.2 hu)
      (MemWkp.sub (by norm_num) isOpen_univ (hφ m).2.2 hu)).trans (add_le_add (hb n) (hb m))
  have hvdiff (nm : ℕ × ℕ) : iteratedWeakSobolevNorm k 2 (fun x => v nm.1 x - v nm.2 x) O ≤
      C * (sobolevApproxError nm.1 + sobolevApproxError nm.2) := by
    exact (hbound (fun x => φ nm.1 x - φ nm.2 x)
      ((hφ nm.1).1.sub (hφ nm.2).1) ((hφ nm.1).2.1.sub (hφ nm.2).2.1)).trans
      (mul_le_mul le_rfl (hdiff nm.1 nm.2) zero_le zero_le)
  have herror : Tendsto (fun nm : ℕ × ℕ => C *
      (sobolevApproxError nm.1 + sobolevApproxError nm.2)) atTop (𝓝 0) := by
    have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
      rw [← prod_atTop_atTop_eq]; exact tendsto_fst
    have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
      rw [← prod_atTop_atTop_eq]; exact tendsto_snd
    have ht := (ENNReal.continuous_const_mul hC).tendsto (0 + 0) |>.comp
      ((sobolevApproxError_tendsto.comp hfst).add
        (sobolevApproxError_tendsto.comp hsnd))
    simpa only [Function.comp_def, add_zero, mul_zero] using ht
  have hCauchy := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herror
    (fun _ => zero_le) hvdiff
  obtain ⟨U, hU, hjet, hUnorm⟩ := exists_sobolev_limit_of_norm_cauchy hO k hv hCauchy
  have huLp : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  have hup := memLp_pullback_of_map_le hc hmap hΦ.continuous.aemeasurable huLp
  let C0 : ℝ≥0∞ := c ^ ((1 / (2 : ℝ≥0∞)).toReal)
  have hC0 : C0 ≠ ⊤ := by simp [C0, hc]
  have hvalbound (n : ℕ) : eLpNorm (fun x => v n x - u (Φ x)) 2 (volume.restrict O) ≤
      C0 * sobolevApproxError n := by
    have hm : MemLp (fun x => φ n x - u x) 2 volume := by
      change MemLp (φ n - u) 2 volume
      simpa only [Measure.restrict_univ] using ((hφ n).2.2.memLp.sub hu.memLp)
    apply (memLp_pullback_of_map_le hc hmap hΦ.continuous.aemeasurable hm).2.trans
    apply mul_le_mul le_rfl _ zero_le zero_le
    apply le_trans _ (hb n)
    simpa only [wkpNorm_zero, Measure.restrict_univ] using
      wkpNorm_mono_order (p := (2 : ℝ≥0∞)) (Nat.zero_le k) (fun x => φ n x - u x) univ
  have hval : Tendsto (fun n => eLpNorm (fun x => v n x - u (Φ x)) 2 (volume.restrict O)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => zero_le) hvalbound
    simpa only [Function.comp_def, mul_zero] using (ENNReal.continuous_const_mul hC0).tendsto 0 |>.comp sobolevApproxError_tendsto
  have hUval : Tendsto (fun n => eLpNorm (fun x => v n x - U x) 2 (volume.restrict O)) atTop (𝓝 0) := by
    simpa only [iterWeakPartial_zero] using hjet 0 ![] (Nat.zero_le k)
  have hae : U =ᵐ[volume.restrict O] fun x => u (Φ x) :=
    ae_eq_of_two_memLp_value_limits (fun n => (hv n).memLp) hU.memLp hup.1 hUval hval
  refine ⟨(MemWkp_congr_ae (by norm_num) hO hae).mp hU, ?_⟩
  rw [← wkpNorm_congr_ae (by norm_num) hO hae]
  exact le_of_tendsto_of_tendsto' hUnorm
    ((ENNReal.continuous_const_mul hC).tendsto _ |>.comp hnorm)
    (fun n => hbound (φ n) (hφ n).1 (hφ n).2.1)

#print axioms exists_weak_sobolev_pullback_bound
end Yamabe3.Analysis.UniformElliptic
