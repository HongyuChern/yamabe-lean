import Yamabe3.Analysis.NativeCompletionLocalH4
import Yamabe3.Analysis.NativeDelaunayAECollar
import Yamabe3.Analysis.NativeDelaunayGlobalCollar
import Yamabe3.Analysis.SobolevBoundaryGluing
import Yamabe3.Analysis.CompactFamilySobolevBound

/-! One linear function-level extension of the same canonical completion.
Every fixed precompact set away from zero has a bound chosen before orbit,
phase and source. Descent through L2 representatives is a separate step. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 1 \ {(0:E)}

theorem exists_uniform_delaunay_global_collar_ae_operator
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ G : (E → ℝ) →ₗ[ℝ] (E → ℝ),
      (∀ u v : E → ℝ, u =ᵐ[volume] v → G u =ᵐ[volume] G v) ∧
      (∀ (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source),
        EqOn (G (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)))
          (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)) O) ∧
      ∀ V : Set E, IsOpen V → IsCompact (closure V) → (∀ x ∈ closure V, x ≠ 0) →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source),
          MemWkp 4 2 (G (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f))) V ∧
          iteratedWeakSobolevNorm 4 2 (G (toL2 nativeWeakEuclideanD O
            (delaunayPhaseCompletion hκ0 hκ1 p f))) V ≤ C*ENNReal.ofReal ‖f.1‖ := by
  obtain ⟨U,L,C,hU,hs,hC,hAE,hL⟩ := exists_uniform_delaunay_compact_H4_collar_ae_operator hκ0 hκ1
  let G := sphereCollarGlueLinear L
  let J := DelaunayPhaseData κ × HalfEndHighH2Source
  let Z (j : J) : E → ℝ := toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 j.1 j.2)
  let T (j : J) : E → ℝ := G (Z j)
  have hl : ∀ a : E, a ≠ 0 → ∃ (N : Set E) (D : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ D ≠ ⊤ ∧ ∀ j : J,
        MemWkp 4 2 (T j) N ∧ iteratedWeakSobolevNorm 4 2 (T j) N ≤ D*ENNReal.ofReal ‖j.2.1‖ := by
    intro a ha
    rcases lt_trichotomy ‖a‖ 1 with hi | he | ho
    · have haO : a ∈ O := ⟨by simpa only [mem_ball,dist_zero_right] using hi,ha⟩
      obtain ⟨N,D,haN,hN,hNO,hD,hb⟩ := exists_uniform_completion_local_H4_bound hκ0 hκ1 haO
      refine ⟨N,D,haN,hN,hD,?_⟩
      intro j
      have heq : T j =ᵐ[volume.restrict N] Z j := by
        filter_upwards [ae_restrict_mem hN.measurableSet] with x hx
        exact sphereCollarGlue_inside (Z j) (L (Z j)) (hNO hx).1
      refine ⟨(MemWkp_congr_ae (by norm_num) hN heq).mpr (hb j.1 j.2).1,?_⟩
      rw [wkpNorm_congr_ae (k := 4) (by norm_num) hN heq]
      exact (hb j.1 j.2).2
    · let N := U \ {(0:E)}
      have hN : IsOpen N := hU.sdiff isClosed_singleton
      refine ⟨N,C,⟨hs (by simpa only [mem_sphere,dist_zero_right] using he),ha⟩,hN,hC,?_⟩
      intro j
      have hj := hL j.1 j.2
      have heq : T j =ᵐ[volume.restrict N] L (Z j) := by
        filter_upwards [ae_restrict_mem hN.measurableSet] with x hx
        exact sphereCollarGlue_on_overlap hj.2.2.2 hx
      refine ⟨(MemWkp_congr_ae (by norm_num) hN heq).mpr
        (hj.2.1.mono_set (by norm_num) hN (subset_univ N)),?_⟩
      rw [wkpNorm_congr_ae (k := 4) (by norm_num) hN heq]
      exact (wkpNorm_mono_set (by norm_num) hN (subset_univ N) hj.2.1).trans hj.2.2.1
    · let N : Set E := {x | 1 < ‖x‖}
      have hN : IsOpen N := isOpen_lt continuous_const continuous_norm
      refine ⟨N,C,ho,hN,hC,?_⟩
      intro j
      have hj := hL j.1 j.2
      have heq : T j =ᵐ[volume.restrict N] L (Z j) := by
        filter_upwards [ae_restrict_mem hN.measurableSet] with x hx
        exact if_neg (not_lt.mpr (le_of_lt hx))
      refine ⟨(MemWkp_congr_ae (by norm_num) hN heq).mpr
        (hj.2.1.mono_set (by norm_num) hN (subset_univ N)),?_⟩
      rw [wkpNorm_congr_ae (k := 4) (by norm_num) hN heq]
      exact (wkpNorm_mono_set (by norm_num) hN (subset_univ N) hj.2.1).trans hj.2.2.1
  have hGAE : ∀ u v : E → ℝ, u =ᵐ[volume] v → G u =ᵐ[volume] G v := by
    intro u v huv
    filter_upwards [huv,hAE u v huv] with x hx hLx
    change sphereCollarGlue u (L u) x = sphereCollarGlue v (L v) x
    by_cases hn : ‖x‖ < 1 <;> simp [sphereCollarGlue,hn,hx,hLx]
  refine ⟨G,hGAE,fun p f x hx => sphereCollarGlue_inside _ _ hx.1,?_⟩
  intro V hV hVc hV0
  obtain ⟨D,hD,hb⟩ := exists_compact_family_sobolev_bound 4 hV hVc T
    (fun j : J => ENNReal.ofReal ‖j.2.1‖) (fun a ha => hl a (hV0 a ha))
  exact ⟨D,hD,fun p f => hb (p,f)⟩

#print axioms exists_uniform_delaunay_global_collar_ae_operator
end Yamabe3.Analysis.UniformElliptic
