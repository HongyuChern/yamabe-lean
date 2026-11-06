import Yamabe3.Analysis.SobolevWeakPullback
import Yamabe3.Analysis.SmoothMapCompactExtension

/-! Actual local Sobolev inputs under a smooth coordinate map. A cutoff
inside the physical source neighborhood discharges compact support; no
vanishing on the coordinate boundary is imposed on the original input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The globally extended map is only an implementation device: the
conclusion uses the actual original local map and the same input. -/
theorem exists_local_map_sobolev_bound (k : ℕ)
    {O S : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hS : IsOpen S) (hOS : closure O ⊆ S) (e : E → E) (he : ContDiffOn ℝ ∞ e S)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (hmap : (volume.restrict O).map e ≤ c • volume) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ,
      MemWkp k 2 u univ → HasCompactSupport u →
      MemWkp k 2 (fun x => u (e x)) O ∧
      iteratedWeakSobolevNorm k 2 (fun x => u (e x)) O ≤ C * iteratedWeakSobolevNorm k 2 u univ := by
  obtain ⟨Φ, hΦ, -, heq⟩ := exists_smooth_map_eq_on_compact hS hOc hOS e he
  have hae : Φ =ᵐ[volume.restrict O] e := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact heq (subset_closure hx)
  have hmapΦ : (volume.restrict O).map Φ ≤ c • volume := by
    rw [Measure.map_congr hae]
    exact hmap
  obtain ⟨C, hC, hb⟩ := exists_weak_sobolev_pullback_bound k hO hOc Φ hΦ c hc hmapΦ
  refine ⟨C, hC, ?_⟩
  intro u hu huc
  have hh := hb u hu huc
  have hcomp : (fun x => u (Φ x)) =ᵐ[volume.restrict O] fun x => u (e x) :=
    hae.mono (fun x hx => congrArg u hx)
  exact ⟨(MemWkp_congr_ae (by norm_num) hO hcomp).mp hh.1,
    (wkpNorm_congr_ae (k := k) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO hcomp) ▸ hh.2⟩

/-- A coefficient smooth only on the chart is a genuine bounded multiplier
on a compactly contained coordinate domain. -/
theorem exists_local_sobolev_multiplier_bound (k : ℕ)
    {O S : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hS : IsOpen S) (hOS : closure O ⊆ S) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a S) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ, MemWkp k 2 u O →
      MemWkp k 2 (fun x => a x * u x) O ∧
      iteratedWeakSobolevNorm k 2 (fun x => a x * u x) O ≤ C * iteratedWeakSobolevNorm k 2 u O := by
  obtain ⟨A, hA, -, heq⟩ := exists_smooth_map_eq_on_compact hS hOc hOS a ha
  obtain ⟨C, hC, hb⟩ := exists_compact_sobolev_multiplier_bound k hO hOc A hA
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hae : (fun x => A x * u x) =ᵐ[volume.restrict O] fun x => a x * u x := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    rw [heq (subset_closure hx)]
  exact ⟨(MemWkp_congr_ae (by norm_num) hO hae).mp
    (memWkp_mul_smooth_of_isCompact_closure k hO hOc hu hA),
    (wkpNorm_congr_ae (k := k) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO hae) ▸ (hb u hu)⟩

/-- Local Hk of the physical input suffices. The cutoff is chosen before
that input; the bound preserves the actual coordinate composition. -/
theorem exists_local_source_pullback_bound (k : ℕ)
    {O S W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hS : IsOpen S) (hOS : closure O ⊆ S) (hW : IsOpen W)
    (e : E → E) (he : ContDiffOn ℝ ∞ e S) (heW : e '' closure O ⊆ W)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (hmap : (volume.restrict O).map e ≤ c • volume) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ, MemWkp k 2 u W →
      MemWkp k 2 (fun x => u (e x)) O ∧
      iteratedWeakSobolevNorm k 2 (fun x => u (e x)) O ≤ C * iteratedWeakSobolevNorm k 2 u W := by
  have hK : IsCompact (e '' closure O) := hOc.image_of_continuousOn (he.continuousOn.mono hOS)
  obtain ⟨χ, hχ, hχc, -, hone, hs⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hK hW heW
  obtain ⟨Cm, hCm, hm⟩ := exists_localized_sobolev_multiplier_bound k isOpen_univ hW χ hχ hχc hs
  obtain ⟨Cp, hCp, hp⟩ := exists_local_map_sobolev_bound k hO hOc hS hOS e he c hc hmap
  refine ⟨Cp*Cm, ENNReal.mul_ne_top hCp hCm, ?_⟩
  intro u hu
  let v : E → ℝ := fun x => χ x * u x
  have hu' : MemWkp k 2 u (W ∩ univ) := by simpa only [inter_univ] using hu
  have hv : MemWkp k 2 v univ := memWkp_mul_smooth_of_tsupport_subset k isOpen_univ hW hu' hχ hχc hs
  have hvn : iteratedWeakSobolevNorm k 2 v univ ≤ Cm * iteratedWeakSobolevNorm k 2 u W := by
    simpa only [inter_univ] using hm u hu'
  have hh := hp v hv hχc.mul_right
  have hae : (fun x => v (e x)) =ᵐ[volume.restrict O] fun x => u (e x) := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    change χ (e x) * u (e x) = u (e x)
    rw [hone (e x) (mem_image_of_mem e (subset_closure hx)), one_mul]
  refine ⟨(MemWkp_congr_ae (by norm_num) hO hae).mp hh.1, ?_⟩
  rw [← wkpNorm_congr_ae (k := k) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO hae]
  exact hh.2.trans (by simpa only [mul_assoc] using mul_le_mul le_rfl hvn zero_le zero_le)

#print axioms exists_local_map_sobolev_bound
#print axioms exists_local_sobolev_multiplier_bound
#print axioms exists_local_source_pullback_bound
end Yamabe3.Analysis.UniformElliptic
