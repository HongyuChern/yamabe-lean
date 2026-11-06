import Yamabe3.Analysis.WeakDivergenceHigherOrderBound
import Yamabe3.Analysis.WeakDivergenceIdentification

/-! The actual weak variable-coefficient operator with signed potential
is continuous from H(m+2) to Hm. This supports approximation without
replacing the original source by an assumed smooth source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
open Poincare.Analysis.Sobolev.BoundaryLocalization
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def weakDivergencePotential (O : Set E) (a : E → Matrix (Fin d) (Fin d) ℝ) (q u : E → ℝ) : E → ℝ :=
  fun x => weakDivergenceSource O a u x-q x*u x

theorem weakDivergencePotential_congr_ae {O : Set E} (hO : IsOpen O)
    (a : E → Matrix (Fin d) (Fin d) ℝ) (q : E → ℝ) {u v : E → ℝ}
    (huv : u=ᵐ[volume.restrict O] v) :
    weakDivergencePotential O a q u=ᵐ[volume.restrict O] weakDivergencePotential O a q v := by
  filter_upwards [huv,weakDivergenceSource_congr_ae hO a huv] with x hx hd
  simp only [weakDivergencePotential,hx,hd]

theorem exists_weakDivergencePotential_bound (m : ℕ) {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀i j,ContDiff ℝ ∞ (fun x => a x i j)) (q : E → ℝ) (hq : ContDiff ℝ ∞ q) :
    ∃C : ℝ≥0∞,C≠⊤ ∧ ∀u : E → ℝ,MemWkp (m+2) 2 u O →
      MemWkp m 2 (weakDivergencePotential O a q u) O ∧
      iteratedWeakSobolevNorm m 2 (weakDivergencePotential O a q u) O≤C*iteratedWeakSobolevNorm (m+2) 2 u O := by
  obtain ⟨A,hA,haB⟩ := exists_weakDivergenceSource_bound_order m hO hOc a ha
  obtain ⟨B,hB,hb⟩ := exists_compact_sobolev_multiplier_bound m hO hOc q hq
  refine ⟨A+B,ENNReal.add_ne_top.mpr ⟨hA,hB⟩,?_⟩
  intro u hu
  have hum := hu.le_of_le (by omega : m ≤ m+2)
  have hqu := memWkp_mul_smooth_of_isCompact_closure m hO hOc hum hq
  have hdiv := haB u hu
  refine ⟨MemWkp.sub (by norm_num) hO hdiv.1 hqu,?_⟩
  exact (sobolevNorm_sub_le hO hdiv.1 hqu).trans
    ((add_le_add hdiv.2 ((hb u hum).trans (mul_le_mul le_rfl
      (wkpNorm_mono_order (by omega : m ≤ m+2) u O) zero_le zero_le))).trans_eq (add_mul _ _ _).symm)

theorem exists_weakDivergencePotential_difference_bound (m : ℕ) {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀i j,ContDiff ℝ ∞ (fun x => a x i j)) (q : E → ℝ) (hq : ContDiff ℝ ∞ q) :
    ∃C : ℝ≥0∞,C≠⊤ ∧ ∀u v : E → ℝ,MemWkp (m+2) 2 u O → MemWkp (m+2) 2 v O →
      iteratedWeakSobolevNorm m 2 (fun x => weakDivergencePotential O a q u x-weakDivergencePotential O a q v x) O≤
        C*iteratedWeakSobolevNorm (m+2) 2 (fun x => u x-v x) O := by
  obtain ⟨C,hC,hb⟩ := exists_weakDivergencePotential_bound m hO hOc a ha q hq
  refine ⟨C,hC,?_⟩
  intro u v hu hv
  have he : (fun x => weakDivergencePotential O a q u x-weakDivergencePotential O a q v x)=ᵐ[volume.restrict O]
      weakDivergencePotential O a q (fun x => u x-v x) := by
    filter_upwards [weakDivergenceSource_sub_ae hO a (hu.le_of_le (by omega : 2 ≤ m+2))
      (hv.le_of_le (by omega : 2 ≤ m+2))] with x hx
    simp only [weakDivergencePotential,hx]
    ring
  rw [wkpNorm_congr_ae (k:=m) (by norm_num) hO he]
  exact (hb _ (MemWkp.sub (by norm_num) hO hu hv)).2

#print axioms weakDivergencePotential_congr_ae
#print axioms exists_weakDivergencePotential_bound
#print axioms exists_weakDivergencePotential_difference_bound
end Yamabe3.Analysis.UniformElliptic
