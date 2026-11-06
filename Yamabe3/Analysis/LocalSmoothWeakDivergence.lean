import Yamabe3.Analysis.SmoothChartDivergenceIdentity
import Yamabe3.Analysis.UniformElliptic.LocalDivergenceEquation

/-! The classical/weak operator identity needs only local smoothness.
An actual compact extension preserves the scalar germ on the retained set. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem weakDivergenceSource_smoothOn_ae
    {O U : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hU : IsOpen U) (hOU : closure O⊆U)
    (a : E → Matrix (Fin 3) (Fin 3) ℝ)
    (ha : ∀ i j,ContDiff ℝ ∞ (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    MemWkp 2 2 u O ∧ weakDivergenceSource O a u =ᵐ[volume.restrict O] principalSource a u := by
  obtain ⟨v,hv,hvc,hvu⟩ := exists_smooth_compact_extension_near_compact hU hOc hOU hu
  have hvm : MemWkp 2 2 v O :=
    (MemWkp_of_smooth_compactSupport isOpen_univ hv hvc (subset_univ _) (by norm_num) 2).mono_set
      (by norm_num) hO (subset_univ _)
  have hae : v =ᵐ[volume.restrict O] u := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact (hvu x (subset_closure hx)).self_of_nhds
  have hclass : principalSource a v =ᵐ[volume.restrict O] principalSource a u := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact principalSource_eq_of_eventuallyEq a (hvu x (subset_closure hx))
  exact ⟨(MemWkp_congr_ae (by norm_num) hO hae).mp hvm,
    (weakDivergenceSource_congr_ae hO a hae).symm.trans
      ((weakDivergenceSource_smooth_ae hO hOc a ha hv hvm).trans hclass)⟩

#print axioms weakDivergenceSource_smoothOn_ae
end Yamabe3.Analysis.UniformElliptic
