import Yamabe3.Analysis.NativePotentialErrorScaling
import Yamabe3.Analysis.NativePrincipalErrorRows
import Yamabe3.Analysis.DelaunayPhaseData

/-! The genuine scalar/density potential defect acts on every original
H4 graph row. Its coefficient jets come from the actual Delaunay ODE. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_native_potential_error_rows
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0 = 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ a ∈ Λ,
      ∀ (κ : ℝ) (p : DelaunayPhaseData κ) (v : HalfEndPhysicalH4Graph) (i : HalfEndPhysicalSliceIndex),
      let h : E → ℝ := fun x => radialScale ‖x‖ *
        nativeNormalizedPotentialError (g a) ε p.orbit p.phase
          (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) (Real.exp (-i.1) • x)
      MemWkp 2 2 h halfEndSourceAnnulus ∧
        iteratedWeakSobolevNorm 2 2 h halfEndSourceAnnulus ≤ ENNReal.ofReal τ*ENNReal.ofReal ‖v‖ := by
  obtain ⟨δ,hδ,hd⟩ := exists_uniform_small_finite_native_delaunay_potential_error Λ g hρ 2
    (show 0 < τ/49 by positivity)
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro ε hε hεδ a ha κ p v i
  let U := halfEndWeightedPhysicalSliceMap v.1.1 i
  let c := nativeDelaunayPotentialError (g a) (ε*Real.exp (-i.1)) p.orbit (p.phase+i.1)
  have he : Real.exp (-i.1) ≤ 2 := by
    have hh := Real.exp_le_exp.mpr (show -i.1 ≤ Real.log 2 by linarith [i.2])
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 2)] using hh
  have hr : ε*Real.exp (-i.1) < δ := by nlinarith
  have hsub : halfEndSourceAnnulus ⊆ halfEndBasicAnnulus :=
    subset_closure.trans NativeJacobianAnnulus.closure_sourceAnnulus_subset_outer
  have hu := ((v.2 i).1).mono_set (by norm_num : (1:ℝ≥0∞) ≤ 2) halfEndSourceAnnulus_isOpen hsub
  have hcoeff := hd (ε*Real.exp (-i.1)) (mul_nonneg hε (Real.exp_pos _).le) hr a ha
    p.orbit p.smooth (fun t => ⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩) p.ode
    (p.phase+i.1)
  have hc : ContDiffOn ℝ ∞ c halfEndBasicAnnulus := by
    intro x hx
    exact (contDiffAt_nativeDelaunayPotentialError (g a) _ p.smooth _
      (norm_pos_iff.mp (by linarith [hx.1]))).contDiffWithinAt
  have hcjet : ∀ j ≤ 2, ∀ x ∈ halfEndSourceAnnulus, ‖iteratedFDeriv ℝ j c x‖ ≤ τ/49 := by
    intro j hj x hx
    exact hcoeff j hj x (by linarith [hx.1]) (by linarith [hx.2])
  have hh := weak_local_multiplier_explicit_bound 2 halfEndSourceAnnulus_isOpen
    NativeJacobianAnnulus.sourceAnnulus_precompact halfEndBasicAnnulus_isOpen
    NativeJacobianAnnulus.closure_sourceAnnulus_subset_outer hc (hu.le_of_le (by omega : 2≤4))
    (show 0 ≤ τ/49 by positivity) hcjet
  norm_num only [Nat.cast_ofNat,show (1+2*(3:ℝ≥0∞))^2=49 by norm_num] at hh
  have hf : (49:ℝ≥0∞)*ENNReal.ofReal (τ/49) = ENNReal.ofReal τ := by
    rw [← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤49)]
    congr 1
    ring
  rw [hf] at hh
  have heq : (fun x => radialScale ‖x‖ * nativeNormalizedPotentialError (g a) ε p.orbit p.phase
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) (Real.exp (-i.1) • x)) =ᵐ[volume.restrict halfEndSourceAnnulus]
      fun x => c x*U x := by
    filter_upwards [ae_restrict_mem halfEndSourceAnnulus_isOpen.measurableSet] with x hx
    exact nativeNormalizedPotentialError_slice _ _ _ _ _ _ (norm_pos_iff.mp (by linarith [hx.1]))
  refine ⟨(MemWkp_congr_ae (by norm_num) halfEndSourceAnnulus_isOpen heq).mpr hh.1,?_⟩
  rw [wkpNorm_congr_ae (k := 2) (by norm_num) halfEndSourceAnnulus_isOpen heq]
  exact hh.2.trans (mul_le_mul le_rfl
    ((wkpNorm_mono_order (by omega : 2≤4) U halfEndSourceAnnulus).trans
      ((wkpNorm_mono_set (by norm_num) halfEndSourceAnnulus_isOpen hsub (v.2 i).1).trans
        (halfEndWeightedPhysicalSliceMap_norm_le v i))) zero_le zero_le)

#print axioms exists_uniform_native_potential_error_rows
end Yamabe3.Analysis.UniformElliptic
