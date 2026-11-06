import Yamabe3.Analysis.CompactSobolevPatching
import Yamabe3.Analysis.UniformElliptic.LocalUniformJet
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Density

/-! A fixed finite smooth family on a precompact domain has a genuine
Sobolev bound uniform in its scalar coefficients. Actual compact
extensions establish membership before the finite weak sum estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem memWkp_of_smooth_near_precompact (k:ℕ) {O W:Set E}
    (hO:IsOpen O) (hOc:IsCompact (closure O)) (hW:IsOpen W) (hOW:closure O⊆W)
    {u:E→ℝ} (hu:ContDiffOn ℝ ∞ u W) : MemWkp k 2 u O := by
  obtain ⟨v,hv,hvc,he⟩:=exists_smooth_compact_extension_near_compact hW hOc hOW hu
  have hm:MemWkp k 2 v univ:=MemWkp_of_smooth_compactSupport isOpen_univ hv hvc (subset_univ _) (by norm_num) k
  apply (MemWkp_congr_ae (by norm_num) hO ?_).mp (hm.mono_set (by norm_num) hO (subset_univ _))
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  exact (he x (subset_closure hx)).self_of_nhds

theorem exists_finite_smooth_sobolev_bound {ι:Type*} (s:Finset ι) (b:ι→E→ℝ)
    (k:ℕ) {O W:Set E} (hO:IsOpen O) (hOc:IsCompact (closure O))
    (hW:IsOpen W) (hOW:closure O⊆W) (hb:∀i∈s,ContDiffOn ℝ ∞ (b i) W) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(c:ι→ℝ) (B:ℝ), (∀i∈s,‖c i‖≤B) →
      MemWkp k 2 (fun x=>∑i∈s,c i*b i x) O ∧
      iteratedWeakSobolevNorm k 2 (fun x=>∑i∈s,c i*b i x) O≤C*ENNReal.ofReal B := by
  have hm (i:ι) (hi:i∈s):MemWkp k 2 (b i) O:=
    memWkp_of_smooth_near_precompact k hO hOc hW hOW (hb i hi)
  refine ⟨∑i∈s,iteratedWeakSobolevNorm k 2 (b i) O,
    ENNReal.sum_ne_top.mpr (fun i hi=>(wkpNorm_lt_top_of_memWkp (hm i hi)).ne),?_⟩
  intro c B hB
  have hh:=finite_sobolev_sum_with_bound hO k s (fun i x=>c i*b i x)
    (fun i hi=>MemWkp.const_smul (by norm_num) hO (hm i hi) (c i))
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [wkpNorm_const_smul (by norm_num) hO (hm i hi),←ofReal_norm]
  exact (mul_le_mul (ENNReal.ofReal_le_ofReal (hB i hi)) le_rfl zero_le zero_le).trans_eq (mul_comm _ _)

#print axioms memWkp_of_smooth_near_precompact
#print axioms exists_finite_smooth_sobolev_bound
end Yamabe3.Analysis.UniformElliptic
