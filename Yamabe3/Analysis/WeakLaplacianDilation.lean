import Yamabe3.Analysis.WeakDilationNorm
import Yamabe3.Analysis.WeakLaplacianEquation

/-! Actual weak derivative and Laplacian scaling. Volume-a.e. identities
are transported by the nonzero dilation measure map, not by substitution
in an arbitrary null set. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem ae_comp_dilation {r : ℝ} (hr : r ≠ 0) {O : Set E} {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict O] v) :
    (fun x : E => u (r • x)) =ᵐ[volume.restrict ((fun x : E => r • x) ⁻¹' O)]
      fun x => v (r • x) := by
  apply ae_eq_comp (continuous_id.const_smul r).measurable.aemeasurable
  change u =ᵐ[Measure.map (fun x : E => r • x) (volume.restrict ((fun x : E => r • x) ⁻¹' O))] v
  rw [map_restrict_volume_dilation hr]
  exact Measure.ae_smul_measure huv _

theorem chosenWeakPartial_comp_dilation {r : ℝ} (hr : r ≠ 0)
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} (hu : MemWkp 1 2 u O) (i : Fin d) :
    chosenWeakPartial' 2 i (fun x : E => u (r • x)) ((fun x : E => r • x) ⁻¹' O)
      =ᵐ[volume.restrict ((fun x : E => r • x) ⁻¹' O)]
      fun x => r * chosenWeakPartial' 2 i u O (r • x) := by
  have hp : (1:ℝ≥0∞) ≤ 2 := by norm_num
  have hW := hO.preimage (continuous_id.const_smul r)
  have hc := memWkp_comp_dilation hr hO hp 1 hu
  have hg := (memLp_comp_dilation hr (chosenWeakPartial'_memLp_of_mem hu.memW1p i)).const_mul r
  exact HasWeakPartialDeriv.ae_eq hW
    (chosenWeakPartial'_isWeakPartial_of_mem hc.memW1p i)
    (hasWeakPartialDeriv_comp_dilation hr (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i))
    ((chosenWeakPartial'_memLp_of_mem hc.memW1p i).locallyIntegrable hp)
    (hg.locallyIntegrable hp)

theorem weakNegativeLaplacian_comp_dilation {r : ℝ} (hr : r ≠ 0)
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} (hu : MemWkp 2 2 u O) :
    weakNegativeLaplacian ((fun x : E => r • x) ⁻¹' O) (fun x => u (r • x))
      =ᵐ[volume.restrict ((fun x : E => r • x) ⁻¹' O)]
      fun x => r^2 * weakNegativeLaplacian O u (r • x) := by
  let W := (fun x : E => r • x) ⁻¹' O
  have hW : IsOpen W := hO.preimage (continuous_id.const_smul r)
  have hp : (1:ℝ≥0∞) ≤ 2 := by norm_num
  have hd (i : Fin d) :
      chosenWeakPartial' 2 i (chosenWeakPartial' 2 i (fun x : E => u (r • x)) W) W
        =ᵐ[volume.restrict W] fun x => r^2 * chosenWeakPartial' 2 i (chosenWeakPartial' 2 i u O) O (r • x) := by
    have h1 := chosenWeakPartial_comp_dilation hr hO (hu.le_of_le (by omega)) i
    have h2 := chosenWeakPartial_comp_dilation hr hO (hu.chosenWeakPartial_mem i) i
    have hc := memWkp_comp_dilation hr hO hp 1 (hu.chosenWeakPartial_mem i)
    have he := (chosenWeakPartial'_ae_congr hp hW h1 i).trans
      (chosenWeakPartial'_const_smul_ae hp hW hc.memW1p r i)
    filter_upwards [he,h2] with x hx hy
    rw [hx,hy]
    ring
  filter_upwards [eventually_all.mpr hd] with x hx
  change -(∑ i : Fin d, chosenWeakPartial' 2 i
      (chosenWeakPartial' 2 i (fun x : E => u (r • x)) W) W x) =
    r^2 * -(∑ i : Fin d, chosenWeakPartial' 2 i (chosenWeakPartial' 2 i u O) O (r • x))
  simp only [hx,← Finset.mul_sum]
  ring

theorem weakNegativeLaplacian_const_mul {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : MemWkp 2 2 u O) (c : ℝ) :
    weakNegativeLaplacian O (fun x => c*u x) =ᵐ[volume.restrict O]
      fun x => c*weakNegativeLaplacian O u x := by
  have he (i : Fin d) := iterWeakPartial_const_smul_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
    hO (fun _ : Fin 2 => i) hu c
  filter_upwards [eventually_all.mpr he] with x hx
  simp only [weakNegativeLaplacian,hx,← Finset.mul_sum]
  ring

#print axioms ae_comp_dilation
#print axioms chosenWeakPartial_comp_dilation
#print axioms weakNegativeLaplacian_comp_dilation
#print axioms weakNegativeLaplacian_const_mul
end Yamabe3.Analysis.UniformElliptic
