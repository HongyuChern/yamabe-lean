import Yamabe3.Analysis.BoundaryPhysicalLinearExtension
import Yamabe3.Analysis.EuclideanChartAE

/-! The constructed local extension is independent of physical L2
representatives. Zero input norm forces zero output norm; no pointwise
restriction of volume-a.e. equality to a boundary is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ENNReal Topology Manifold ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.BoundaryTangential
open PoincareMT.LeviCivitaData.Dirichlet
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem linear_chart_extension_congr_ae
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    (χ : E → ℝ) {U N : Set E} (hU : IsOpen U) (hN : IsOpen N)
    (L : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞)
    (hb : ∀ u : E → ℝ, MemWkp 4 2 (chartPullback e (fun y => χ y*u y)) (U ∩ halfSpace d) →
      MemWkp 4 2 (L u) N ∧ iteratedWeakSobolevNorm 4 2 (L u) N ≤
        C*iteratedWeakSobolevNorm 4 2 (chartPullback e (fun y => χ y*u y)) (U ∩ halfSpace d))
    {u v : E → ℝ} (huv : u =ᵐ[volume] v) : L u =ᵐ[volume.restrict N] L v := by
  have hW : IsOpen (U ∩ halfSpace d) := hU.inter isOpen_halfSpace
  have hz : (fun y => χ y*(u-v) y) =ᵐ[volume] (fun _ => (0:ℝ)) := by
    filter_upwards [huv] with y hy
    simp [hy]
  have hp : chartPullback e (fun y => χ y*(u-v) y) =ᵐ[volume.restrict (U ∩ halfSpace d)] (fun _ => (0:ℝ)) := by
    have h := euclidean_chartPullback_congr_ae e he hei hz
    have he0 : chartPullback e (fun _ => (0:ℝ)) = (fun _ => (0:ℝ)) := by
      funext x
      by_cases hx : x ∈ e.source <;> simp [chartPullback,hx]
    rw [he0] at h
    exact ae_restrict_of_ae h
  have hm := (MemWkp_congr_ae (by norm_num : (1:ℝ≥0∞) ≤ 2) hW hp).mpr
    (MemWkp_zero_fun (k := 4) (by norm_num) hW)
  have hh := hb (u-v) hm
  rw [wkpNorm_congr_ae (k := 4) (by norm_num) hW hp,wkpNorm_zero_fun_zero (by norm_num) hW,mul_zero] at hh
  have hzero : eLpNorm (L (u-v)) 2 (volume.restrict N) = 0 := by
    apply le_antisymm _ zero_le
    rw [← wkpNorm_zero]
    exact (wkpNorm_mono_order (by norm_num : 0 ≤ 4) _ N).trans hh.2
  have hae := (eLpNorm_eq_zero_iff hh.1.memLp.aestronglyMeasurable (by norm_num : (2:ℝ≥0∞) ≠ 0)).mp hzero
  filter_upwards [hae] with x hx
  simpa only [map_sub,Pi.sub_apply,Pi.zero_apply,sub_eq_zero] using hx

#print axioms linear_chart_extension_congr_ae
end Yamabe3.Analysis.UniformElliptic
