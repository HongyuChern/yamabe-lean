import Yamabe3.Analysis.NativeDelaunayGlobalAECollar
import Yamabe3.Analysis.NativeAllScaleH4
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

theorem exists_uniform_native_all_scale_ae_H4_extension
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ (G : (E → ℝ) →ₗ[ℝ] (E → ℝ)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      (∀ u v : E → ℝ, u =ᵐ[volume] v → G u =ᵐ[volume] G v) ∧
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
  obtain ⟨G,hGAE,hG,hlocal⟩ := exists_uniform_delaunay_global_collar_ae_operator hκ0 hκ1
  obtain ⟨A,hA,ha⟩ := hlocal (cylinderAnnulus (-3) 6) (isOpen_cylinderAnnulus _ _)
    (isCompact_closure_cylinderAnnulus _ _)
    (fun x hx => cylinderShell_ne_zero (closure_cylinderAnnulus_subset_shell (-3) 6 hx))
  obtain ⟨D,hD,hd⟩ := exists_finite_weighted_dilation_H4_bound
  obtain ⟨B,hB,hb⟩ := exists_uniform_native_weighted_tail_H4_bound hκ0 hκ1
  refine ⟨G,D*A+B,by finiteness,hGAE,hG,hlocal,?_⟩
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

#print axioms exists_uniform_native_all_scale_ae_H4_extension
end Yamabe3.Analysis.UniformElliptic
