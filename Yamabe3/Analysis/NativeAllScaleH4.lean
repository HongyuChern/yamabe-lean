import Yamabe3.Analysis.NativeDelaunayGlobalCollar
import Yamabe3.Analysis.FiniteWeightedDilation

/-! All original graph scales, including the real entrance collar, for
one extension of the same canonical half-end completion. The source,
orbit and phase follow the one constant. No graph solver is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 1 \ {(0:E)}

theorem tail_dilation_image {s : ℝ} (hs : 4 ≤ s) :
    halfEndBasicAnnulus ⊆ (fun x : E => Real.exp (-s) • x) ⁻¹' O := by
  have hl : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    have hn : (1/2:ℝ) < ‖x‖ := hx.1
    norm_num [h] at hn
  refine ⟨?_, by simpa only [mem_singleton_iff] using smul_ne_zero (Real.exp_pos (-s)).ne' hx0⟩
  simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ < Real.exp (-s)*2 := mul_lt_mul_of_pos_left hx.2 (Real.exp_pos _)
    _ = Real.exp (-s+Real.log 2) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

theorem exists_uniform_native_all_scale_H4_extension
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ (G : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      (∀ (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source),
        EqOn (G (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)))
          (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f)) O) ∧
      (∀ V : Set E, IsOpen V → IsCompact (closure V) → (∀ x ∈ closure V, x ≠ 0) →
        ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source),
          MemWkp 4 2 (G (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f))) V ∧
          iteratedWeakSobolevNorm 4 2 (G (toL2 nativeWeakEuclideanD O
            (delaunayPhaseCompletion hκ0 hκ1 p f))) V ≤ D*ENNReal.ofReal ‖f.1‖) ∧
      ∀ (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source) (s : ℝ), -Real.log 2 ≤ s →
        let u : E → ℝ := G (toL2 nativeWeakEuclideanD O (delaunayPhaseCompletion hκ0 hκ1 p f))
        MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤ C*ENNReal.ofReal ‖f.1‖ := by
  obtain ⟨G,hG,hlocal⟩ := exists_uniform_delaunay_global_collar_operator hκ0 hκ1
  obtain ⟨A,hA,ha⟩ := hlocal (cylinderAnnulus (-3) 6) (isOpen_cylinderAnnulus _ _)
    (isCompact_closure_cylinderAnnulus _ _)
    (fun x hx => cylinderShell_ne_zero (closure_cylinderAnnulus_subset_shell (-3) 6 hx))
  obtain ⟨D,hD,hd⟩ := exists_finite_weighted_dilation_H4_bound
  obtain ⟨B,hB,hb⟩ := exists_uniform_native_weighted_tail_H4_bound hκ0 hκ1
  refine ⟨G,D*A+B,by finiteness,hG,hlocal,?_⟩
  intro p f s hs
  let z := delaunayPhaseCompletion hκ0 hκ1 p f
  let u : E → ℝ := G (toL2 nativeWeakEuclideanD O z)
  by_cases hs4 : s ≤ 4
  · have hh := hd u (ha p f).1 s hs hs4
    refine ⟨hh.1,hh.2.trans ?_⟩
    calc
      _ ≤ D*(A*ENNReal.ofReal ‖f.1‖) := mul_le_mul le_rfl (ha p f).2 zero_le zero_le
      _ ≤ (D*A+B)*ENNReal.ofReal ‖f.1‖ := by
        rw [← mul_assoc]
        exact mul_le_mul (le_add_right le_rfl) le_rfl zero_le zero_le
  · have hs4' : 4 ≤ s := le_of_lt (lt_of_not_ge hs4)
    have hu : u =ᵐ[volume.restrict O]
        cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg f) := by
      filter_upwards [ae_restrict_mem (isOpen_ball.sdiff isClosed_singleton).measurableSet,
        ae_restrict_of_ae (nativeHalfEndH2SourceCompletion_rep hκ0 hκ1 p.potential
          p.kernel_bound p.potential_nonneg p.potential_smooth f)] with x hx hr
      exact (hG p f hx).trans (hr.trans (indicator_of_mem hx _))
    have ht := ae_comp_dilation (Real.exp_pos (-s)).ne' hu
    have hsmall := ae_restrict_of_ae_restrict_of_subset (tail_dilation_image hs4') ht
    have he : weightedPhysicalDilation s u =ᵐ[volume.restrict halfEndBasicAnnulus]
        actualWeightedHalfEndField hκ0 hκ1 p f s := by
      filter_upwards [hsmall] with x hx
      exact congrArg (fun t : ℝ => Real.exp (3*s/2)*t) hx
    have hh := hb p f s hs4'
    refine ⟨(MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen he).mpr hh.1,?_⟩
    rw [wkpNorm_congr_ae (k := 4) (by norm_num) halfEndBasicAnnulus_isOpen he]
    exact hh.2.trans (mul_le_mul (le_add_left le_rfl) le_rfl zero_le zero_le)

#print axioms tail_dilation_image
#print axioms exists_uniform_native_all_scale_H4_extension
end Yamabe3.Analysis.UniformElliptic
