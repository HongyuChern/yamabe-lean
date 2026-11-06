import Yamabe3.Analysis.WeakDivergenceLocality
import Yamabe3.Analysis.ChartPiecewiseSource

/-! Identify the operator of one actual H2 glued function with its two
physical operators. Only open-side derivative uniqueness and zero volume
of the sphere are used; no volume equality is restricted to the sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem weakDivergenceSource_sphere_piecewise_ae {D W : Set E}
    (hW : IsOpen W) (hWD : W⊆D) (a : E → Matrix (Fin 3) (Fin 3) ℝ)
    {u f g : E → ℝ} (hu : MemWkp 2 2 u W) (hf : MemWkp 2 2 f D) (hg : MemWkp 2 2 g D)
    (hglue : u =ᵐ[volume.restrict W] physicalSplitSource (ball (0:E) 1) f g) :
    weakDivergenceSource W a u =ᵐ[volume.restrict W]
      physicalSplitSource (ball (0:E) 1) (weakDivergenceSource D a f) (weakDivergenceSource D a g) := by
  classical
  let I := W∩ball (0:E) 1
  let J := W∩{x : E | 1<‖x‖}
  have hI : IsOpen I := hW.inter isOpen_ball
  have hJ : IsOpen J := hW.inter (isOpen_lt continuous_const continuous_norm)
  have hi : u =ᵐ[volume.restrict I] f := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hglue,
      ae_restrict_mem hI.measurableSet] with x hx hxi
    exact hx.trans (by simp only [physicalSplitSource,piecewise_eq_of_mem _ _ _ hxi.2])
  have hj : u =ᵐ[volume.restrict J] g := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hglue,
      ae_restrict_mem hJ.measurableSet] with x hx hxj
    have hnot : x∉ball (0:E) 1 := by simpa only [mem_ball,dist_zero_right] using not_lt.mpr hxj.2.le
    exact hx.trans (by simp only [physicalSplitSource,piecewise_eq_of_notMem _ _ _ hnot])
  have hOpI := weakDivergenceSource_same_on_overlap hI inter_subset_left
    (inter_subset_left.trans hWD) a hu hf hi
  have hOpJ := weakDivergenceSource_same_on_overlap hJ inter_subset_left
    (inter_subset_left.trans hWD) a hu hg hj
  have hn : ∀ᵐ x : E ∂volume,x∉sphere (0:E) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0:E) 1)
  filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' hI.measurableSet).mp hOpI),
    ae_restrict_of_ae ((ae_restrict_iff' hJ.measurableSet).mp hOpJ),
    ae_restrict_of_ae hn,ae_restrict_mem hW.measurableSet] with x hxI hxJ hxn hxW
  by_cases hx : x∈ball (0:E) 1
  · simpa only [physicalSplitSource,piecewise_eq_of_mem _ _ _ hx] using hxI ⟨hxW,hx⟩
  · have hne : ‖x‖≠1 := by simpa only [mem_sphere,dist_zero_right] using hxn
    have hle : 1≤‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hx
    have hgt : 1<‖x‖ := lt_of_le_of_ne hle hne.symm
    simpa only [physicalSplitSource,piecewise_eq_of_notMem _ _ _ hx] using hxJ ⟨hxW,hgt⟩

#print axioms weakDivergenceSource_sphere_piecewise_ae
end Yamabe3.Analysis.UniformElliptic
