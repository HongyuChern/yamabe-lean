import Yamabe3.Analysis.WeakDivergenceIdentification

/-! The same H2 weak divergence operator is independent of the retained
open domain. First and second chosen weak derivatives are reconciled
through uniqueness before any source identity is transported. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakDivergenceSource_mono {O W : Set E} (hW : IsOpen W) (hWO : W⊆O)
    (a : E → Matrix (Fin d) (Fin d) ℝ) {u : E → ℝ} (hu : MemWkp 2 2 u O) :
    weakDivergenceSource O a u =ᵐ[volume.restrict W] weakDivergenceSource W a u := by
  have hp (j : Fin d) := chosenWeakPartial'_mono_set_ae (by norm_num : (1:ℝ≥0∞)≤2) hW hWO hu.memW1p j
  have hq (i j : Fin d) := (chosenWeakPartial'_mono_set_ae (by norm_num : (1:ℝ≥0∞)≤2)
    hW hWO (hu.chosenWeakPartial_mem j).memW1p i).trans
    (chosenWeakPartial'_ae_congr (by norm_num : (1:ℝ≥0∞)≤2) hW (hp j) i)
  filter_upwards [eventually_all.mpr hp,eventually_all.mpr (fun i => eventually_all.mpr (hq i))] with x hx hy
  simp only [weakDivergenceSource,hx,hy]

theorem weakDivergenceSource_same_on_overlap {O W V : Set E} (hV : IsOpen V)
    (hVO : V⊆O) (hVW : V⊆W)
    (a : E → Matrix (Fin d) (Fin d) ℝ) {u v : E → ℝ}
    (hu : MemWkp 2 2 u O) (hv : MemWkp 2 2 v W)
    (huv : u =ᵐ[volume.restrict V] v) :
    weakDivergenceSource O a u =ᵐ[volume.restrict V] weakDivergenceSource W a v :=
  (weakDivergenceSource_mono hV hVO a hu).trans
    ((weakDivergenceSource_congr_ae hV a huv).trans (weakDivergenceSource_mono hV hVW a hv).symm)

#print axioms weakDivergenceSource_mono
#print axioms weakDivergenceSource_same_on_overlap
end Yamabe3.Analysis.UniformElliptic
