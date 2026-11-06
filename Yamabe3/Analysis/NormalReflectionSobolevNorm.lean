import Yamabe3.Analysis.WeakNormalScaling
import Yamabe3.Analysis.SobolevOperatorConvergence

/-! Reflection has an actual all-order weak Sobolev norm identity. The
normal derivative signs are retained before taking norms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem eLpNorm_comp_normalReflection (O : Set E) (u : E → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => u (normalScaling (-1) (by norm_num) x)) p
      (volume.restrict ((normalScaling (-1) (by norm_num)) ⁻¹' O))=
      eLpNorm u p (volume.restrict O) := by
  have he : MeasurableEmbedding (normalScaling (d:=d) (-1) (by norm_num)) :=
    (normalScaling (-1) (by norm_num)).toHomeomorph.measurableEmbedding
  change eLpNorm (u∘normalScaling (-1) (by norm_num)) p _=_
  rw [← he.eLpNorm_map_measure,map_restrict_volume_normalScaling]
  norm_num

theorem sobolevNorm_comp_normalReflection {O : Set E} (hO : IsOpen O)
    (k : ℕ) {u : E → ℝ} (hu : MemWkp k 2 u O) :
    iteratedWeakSobolevNorm k 2 (fun x => u (normalScaling (-1) (by norm_num) x))
      ((normalScaling (-1) (by norm_num)) ⁻¹' O)=iteratedWeakSobolevNorm k 2 u O := by
  let N := normalScaling (d:=d) (-1) (by norm_num)
  have hW : IsOpen (N ⁻¹' O) := hO.preimage N.continuous
  induction k generalizing u with
  | zero => simpa only [wkpNorm_zero] using eLpNorm_comp_normalReflection O u 2
  | succ k ih =>
    have hcomp := memWkp_comp_normalScaling (by norm_num : (-1:ℝ)≠0) hO (by norm_num) (k+1) hu
    have heq (i : Fin d) : chosenWeakPartial' 2 i (fun x => u (N x)) (N ⁻¹' O) =ᵐ[volume.restrict (N ⁻¹' O)]
        fun x => normalFactor (-1) i*chosenWeakPartial' 2 i u O (N x) := by
      have hm := memLp_comp_normalScaling (by norm_num : (-1:ℝ)≠0)
        (chosenWeakPartial'_memLp_of_mem hu.memW1p i)
      exact HasWeakPartialDeriv.ae_eq hW
        (chosenWeakPartial'_isWeakPartial_of_mem hcomp.memW1p i)
        (hasWeakPartialDeriv_comp_normalScaling (by norm_num) (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i))
        ((chosenWeakPartial'_memLp_of_mem hcomp.memW1p i).locallyIntegrable (by norm_num))
        ((hm.const_mul (normalFactor (-1) i)).locallyIntegrable (by norm_num))
    rw [wkpNorm_succ_eq k,wkpNorm_succ_eq k,eLpNorm_comp_normalReflection]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [wkpNorm_congr_ae (k:=k) (by norm_num : (1:ℝ≥0∞)≤2) hW (heq i)]
    have hm := memWkp_comp_normalScaling (by norm_num : (-1:ℝ)≠0) hO (by norm_num) k (hu.chosenWeakPartial_mem i)
    rw [wkpNorm_const_smul (by norm_num : (1:ℝ≥0∞)≤2) hW hm (normalFactor (-1) i)]
    have hf : ‖normalFactor (-1) i‖ₑ=(1:ℝ≥0∞) := by
      by_cases hi : i=0 <;> simp [normalFactor,hi]
    rw [hf,one_mul]
    exact ih (hu.chosenWeakPartial_mem i)

#print axioms eLpNorm_comp_normalReflection
#print axioms sobolevNorm_comp_normalReflection
end Yamabe3.Analysis.UniformElliptic
