import Yamabe3.Analysis.NativeFullLocalH4Bound
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
local notation "X" => (E→ℝ) × (E→ℝ)

theorem exists_uniform_full_global_collar_operator
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ G : X →ₗ[ℝ] (E → ℝ),
      (∀ u v : X, u.1 =ᵐ[volume] v.1 → u.2 =ᵐ[volume] v.2 → G u =ᵐ[volume] G v) ∧
      (∀ (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph),
        EqOn (G (fullModelCompletionPair hκ0 hκ1 p f))
          (fun x=>(fullModelCompletionPair hκ0 hκ1 p f).1 x+(fullModelCompletionPair hκ0 hκ1 p f).2 x) O) ∧
      ∀ V : Set E, IsOpen V → IsCompact (closure V) → (∀ x ∈ closure V, x ≠ 0) →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph),
          MemWkp 4 2 (G (fullModelCompletionPair hκ0 hκ1 p f)) V ∧
          iteratedWeakSobolevNorm 4 2 (G (fullModelCompletionPair hκ0 hκ1 p f)) V ≤ C*ENNReal.ofReal ‖f‖ := by
  obtain ⟨U,L,C,hU,hs,hC,hAE,hL⟩ := exists_uniform_full_compact_H4_collar_operator hκ0 hκ1
  let G : X→ₗ[ℝ](E→ℝ) :=
    {toFun:=fun q=>sphereCollarGlue (fun x=>q.1 x+q.2 x) (L q)
     map_add':=by
       intro q r
       funext x
       by_cases h:‖x‖<1 <;> simp [sphereCollarGlue,h] <;> ring
     map_smul':=by
       intro c q
       funext x
       by_cases h:‖x‖<1 <;> simp [sphereCollarGlue,h,mul_add]}
  let J := DelaunayPhaseData κ × HalfEndPhysicalH2SourceGraph
  let Z (j : J) : X := fullModelCompletionPair hκ0 hκ1 j.1 j.2
  let T (j : J) : E → ℝ := G (Z j)
  have hl : ∀ a : E, a ≠ 0 → ∃ (N : Set E) (D : ℝ≥0∞),
      a ∈ N ∧ IsOpen N ∧ D ≠ ⊤ ∧ ∀ j : J,
        MemWkp 4 2 (T j) N ∧ iteratedWeakSobolevNorm 4 2 (T j) N ≤ D*ENNReal.ofReal ‖j.2‖ := by
    intro a ha
    rcases lt_trichotomy ‖a‖ 1 with hi | he | ho
    · have haO : a ∈ O := ⟨by simpa only [mem_ball,dist_zero_right] using hi,ha⟩
      obtain ⟨N,D,haN,hN,hNO,hD,hb⟩ := exists_uniform_full_model_local_H4_bound hκ0 hκ1 haO
      refine ⟨N,D,haN,hN,hD,?_⟩
      intro j
      have heq : T j =ᵐ[volume.restrict N] fullModelPhysicalField hκ0 hκ1 j.1 j.2 := by
        have hr:=ae_restrict_of_ae_restrict_of_subset hNO (fullModelCompletionPair_rep hκ0 hκ1 j.1 j.2)
        filter_upwards [ae_restrict_mem hN.measurableSet,hr] with x hx hr
        exact (sphereCollarGlue_inside (fun y=>(Z j).1 y+(Z j).2 y) (L (Z j)) (hNO hx).1).trans hr
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
  have hGAE : ∀u v:X,u.1 =ᵐ[volume] v.1 → u.2 =ᵐ[volume] v.2 → G u =ᵐ[volume] G v := by
    intro u v h1 h2
    filter_upwards [h1,h2,hAE u v h1 h2] with x hx hy hLx
    change sphereCollarGlue (fun y=>u.1 y+u.2 y) (L u) x =
      sphereCollarGlue (fun y=>v.1 y+v.2 y) (L v) x
    by_cases hn:‖x‖<1 <;> simp [sphereCollarGlue,hn,hx,hy,hLx]
  refine ⟨G,hGAE,fun p f x hx => sphereCollarGlue_inside
    (fun y=>(fullModelCompletionPair hκ0 hκ1 p f).1 y+(fullModelCompletionPair hκ0 hκ1 p f).2 y)
    (L (fullModelCompletionPair hκ0 hκ1 p f)) hx.1,?_⟩
  intro V hV hVc hV0
  obtain ⟨D,hD,hb⟩ := exists_compact_family_sobolev_bound 4 hV hVc T
    (fun j : J => ENNReal.ofReal ‖j.2‖) (fun a ha => hl a (hV0 a ha))
  exact ⟨D,hD,fun p f => hb (p,f)⟩

#print axioms exists_uniform_full_global_collar_operator
end Yamabe3.Analysis.UniformElliptic
