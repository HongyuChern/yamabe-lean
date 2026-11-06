import Yamabe3.Analysis.NativePrincipalErrorScaling
import Yamabe3.Analysis.HalfEndH4GraphRegularity
import Yamabe3.Analysis.WeakH4JetBound

/-! Uniform H2 rows of the actual normalized principal error, on every
allowed scale of the original graph and for the same physical function. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem halfEndWeightedPhysicalSliceMap_contDiffOn_two
    (v : HalfEndPhysicalH4Graph) (i : HalfEndPhysicalSliceIndex) :
    ContDiffOn ℝ 2 (halfEndWeightedPhysicalSliceMap v.1.1 i) halfEndBasicAnnulus := by
  have hm : MapsTo (fun x : E => Real.exp (-i.1) • x) halfEndBasicAnnulus
      (ball (0:E) 4 \ {(0:E)}) := by
    intro x hx
    have he : Real.exp (-i.1) ≤ 2 := by
      have hh := Real.exp_le_exp.mpr (show -i.1 ≤ Real.log 2 by linarith [i.2])
      simpa only [Real.exp_log (by norm_num : (0:ℝ) < 2)] using hh
    have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith [hx.1] : 0 < ‖x‖)
    refine ⟨?_,smul_ne_zero (Real.exp_pos _).ne' hx0⟩
    simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    nlinarith [mul_pos (Real.exp_pos (-i.1)) (show 0 < 2-‖x‖ by linarith [hx.2])]
  exact contDiffOn_const.mul ((halfEndPhysicalH4Graph_contDiffOn_two v).comp
    (contDiff_id.const_smul _).contDiffOn hm)

theorem halfEndWeightedPhysicalSliceMap_norm_le
    (v : HalfEndPhysicalH4Graph) (i : HalfEndPhysicalSliceIndex) :
    iteratedWeakSobolevNorm 4 2 (halfEndWeightedPhysicalSliceMap v.1.1 i)
      halfEndBasicAnnulus ≤ ENNReal.ofReal ‖v‖ :=
  (ENNReal.le_ofReal_iff_toReal_le (wkpNorm_lt_top_of_memWkp (v.2 i).1).ne
    (norm_nonneg v)).mpr (weakSobolevGraph_local_norm_le halfEndBasicAnnulus
      halfEndBasicAnnulus_isOpen 4 halfEndWeightedPhysicalSliceMap v i)

theorem exists_uniform_native_principal_error_rows
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ, (g p).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ p ∈ Λ, (g p).pullbackVolumeDensity id 0 = 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ p ∈ Λ,
      ∀ (v : HalfEndPhysicalH4Graph) (i : HalfEndPhysicalSliceIndex),
      let h : E → ℝ := fun x => Delaunay.radialScale ‖x‖ *
        nativeNormalizedPrincipalError (g p) ε
          (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) (Real.exp (-i.1) • x)
      MemWkp 2 2 h halfEndSourceAnnulus ∧
        iteratedWeakSobolevNorm 2 2 h halfEndSourceAnnulus ≤ ENNReal.ofReal τ*ENNReal.ofReal ‖v‖ := by
  obtain ⟨δ,hδ,hd⟩ := exists_uniform_weak_small_native_geometric_error Λ g hB hρ
    (show (0:ℝ) < 2 by norm_num) hτ
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro ε hε hεδ p hp v i
  let U := halfEndWeightedPhysicalSliceMap v.1.1 i
  have he : Real.exp (-i.1) ≤ 2 := by
    have hh := Real.exp_le_exp.mpr (show -i.1 ≤ Real.log 2 by linarith [i.2])
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 2)] using hh
  have hr : ε*Real.exp (-i.1) < δ := by nlinarith
  have hsub : halfEndSourceAnnulus ⊆ halfEndBasicAnnulus :=
    subset_closure.trans NativeJacobianAnnulus.closure_sourceAnnulus_subset_outer
  have hu := ((v.2 i).1).mono_set (by norm_num : (1:ℝ≥0∞) ≤ 2) halfEndSourceAnnulus_isOpen hsub
  have hu2 := hu.le_of_le (by omega : 2 ≤ 4)
  have huC := halfEndWeightedPhysicalSliceMap_contDiffOn_two v i
  have hball : halfEndSourceAnnulus ⊆ closedBall (0:E) 2 := by
    intro x hx
    simp only [mem_closedBall,dist_zero_right]
    linarith [hx.2]
  have hh := hd (ε*Real.exp (-i.1)) (mul_nonneg hε (Real.exp_pos _).le) hr p hp
    halfEndSourceAnnulus halfEndSourceAnnulus_isOpen NativeJacobianAnnulus.sourceAnnulus_precompact
    hball U hu
  have ha := nativeWeakScaledGeometricError_classical_ae (g p) (ε*Real.exp (-i.1))
    halfEndSourceAnnulus_isOpen NativeJacobianAnnulus.sourceAnnulus_precompact
    halfEndBasicAnnulus_isOpen NativeJacobianAnnulus.closure_sourceAnnulus_subset_outer huC hu2
  have heq : (fun x => Delaunay.radialScale ‖x‖ * nativeNormalizedPrincipalError (g p) ε
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) (Real.exp (-i.1) • x)) =ᵐ[volume.restrict halfEndSourceAnnulus]
      nativeWeakScaledGeometricError (g p) (ε*Real.exp (-i.1)) halfEndSourceAnnulus U := by
    filter_upwards [ae_restrict_mem halfEndSourceAnnulus_isOpen.measurableSet,ha] with x hx hxAE
    rw [nativeNormalizedPrincipalError_slice _ _ _ _ (norm_pos_iff.mp (by linarith [hx.1]))]
    exact (nativePrincipalError_eq_classical _ _ (huC.contDiffAt
      (halfEndBasicAnnulus_isOpen.mem_nhds (hsub hx)))).trans hxAE.symm
  refine ⟨(MemWkp_congr_ae (by norm_num) halfEndSourceAnnulus_isOpen heq).mpr hh.1,?_⟩
  rw [wkpNorm_congr_ae (k := 2) (by norm_num) halfEndSourceAnnulus_isOpen heq]
  exact hh.2.trans (mul_le_mul le_rfl
    ((wkpNorm_mono_set (by norm_num) halfEndSourceAnnulus_isOpen hsub (v.2 i).1).trans
      (halfEndWeightedPhysicalSliceMap_norm_le v i)) zero_le zero_le)

#print axioms halfEndWeightedPhysicalSliceMap_contDiffOn_two
#print axioms halfEndWeightedPhysicalSliceMap_norm_le
#print axioms exists_uniform_native_principal_error_rows
end Yamabe3.Analysis.UniformElliptic
