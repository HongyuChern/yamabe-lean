import PoincareLib.Analysis.Elliptic.Regularity.Iteration.LocalSobolev
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Local weak Sobolev gluing across the actual unit sphere.  The collar
must agree with the same inside representative on an open overlap.
No restriction of a volume-a.e. identity to the boundary is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def sphereCollarGlue (u v : E → ℝ) (x : E) : ℝ :=
  if ‖x‖ < 1 then u x else v x

theorem sphereCollarGlue_inside (u v : E → ℝ) :
    EqOn (sphereCollarGlue u v) u (Metric.ball 0 1) := by
  intro x hx
  exact if_pos (by simpa only [Metric.mem_ball, dist_zero_right] using hx)

theorem sphereCollarGlue_on_overlap {u v : E → ℝ} {U : Set E}
    (heq : EqOn v u (U ∩ (Metric.ball 0 1 \ {(0:E)}))) :
    EqOn (sphereCollarGlue u v) v (U \ {(0:E)}) := by
  intro x hx
  by_cases h : ‖x‖ < 1
  · rw [sphereCollarGlue, if_pos h]
    exact (heq ⟨hx.1, ⟨by simpa only [Metric.mem_ball, dist_zero_right] using h, hx.2⟩⟩).symm
  · exact if_neg h

theorem memWkpLocally_congr_ae {k : ℕ} {O : Set E} {u v : E → ℝ}
    (h : u =ᵐ[volume.restrict O] v) (hu : MemWkpLocally k u O) :
    MemWkpLocally k v O := by
  intro x hx
  obtain ⟨W,hW,hxW,hWO,huW⟩ := hu x hx
  exact ⟨W,hW,hxW,hWO,(MemWkp_congr_ae (by norm_num) hW
    (ae_restrict_of_ae_restrict_of_subset hWO h)).mp huW⟩

theorem memWkpLocally_sphereCollarGlue {k : ℕ} {u v : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hs : Metric.sphere (0:E) 1 ⊆ U)
    (heq : EqOn v u (U ∩ (Metric.ball 0 1 \ {(0:E)})))
    (hu : MemWkpLocally k u (Metric.ball 0 1 \ {(0:E)}))
    (hv : MemWkp k 2 v univ) :
    MemWkpLocally k (sphereCollarGlue u v) ({(0:E)}ᶜ) := by
  intro x hx
  rcases lt_trichotomy ‖x‖ 1 with hi | he | ho
  · have hxO : x ∈ Metric.ball 0 1 \ {(0:E)} :=
      ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hi, hx⟩
    obtain ⟨W,hW,hxW,hWO,huW⟩ := hu x hxO
    refine ⟨W,hW,hxW,fun y hy => (hWO hy).2, ?_⟩
    apply (MemWkp_congr_ae (by norm_num) hW ?_).mp huW
    filter_upwards [ae_restrict_mem hW.measurableSet] with y hy
    exact (sphereCollarGlue_inside u v (hWO hy).1).symm
  · let W := U \ {(0:E)}
    have hW : IsOpen W := hU.sdiff isClosed_singleton
    have hh : MemWkp k 2 v W := hv.mono_set (by norm_num) hW (subset_univ _)
    refine ⟨W,hW,⟨hs (by simpa only [Metric.mem_sphere, dist_zero_right] using he),hx⟩,
      fun y hy => hy.2, ?_⟩
    apply (MemWkp_congr_ae (by norm_num) hW ?_).mp hh
    filter_upwards [ae_restrict_mem hW.measurableSet] with y hy
    exact (sphereCollarGlue_on_overlap heq hy).symm
  · let W : Set E := {y | 1 < ‖y‖}
    have hW : IsOpen W := isOpen_lt continuous_const continuous_norm
    have hh : MemWkp k 2 v W := hv.mono_set (by norm_num) hW (subset_univ _)
    refine ⟨W,hW,ho,?_, ?_⟩
    · intro y hy
      have : y ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hy)
      simpa using this
    · apply (MemWkp_congr_ae (by norm_num) hW ?_).mp hh
      filter_upwards [ae_restrict_mem hW.measurableSet] with y hy
      exact (if_neg (not_lt.mpr (le_of_lt hy))).symm

#print axioms memWkpLocally_sphereCollarGlue
end Yamabe3.Analysis.UniformElliptic
