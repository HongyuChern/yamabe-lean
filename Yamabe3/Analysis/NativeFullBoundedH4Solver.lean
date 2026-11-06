import Yamabe3.Analysis.NativeFullContinuousLinearity
import Yamabe3.Analysis.HalfEndGraphNorms

/-! The actual same-source half-end operator into the original complete
physical H4 graph. Both the retained value-coordinate norm and every
weighted weak-jet row are bounded. This constructs the operator; it does
not assume a high-regularity inverse or change the original source space. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 1 \ {(0:E)}
local notation "P" => ({(0:E)}ᶜ : Set E)

theorem exists_uniform_full_bounded_H4_solver
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : DelaunayPhaseData κ,
      ∃ T : HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph,
        ‖T‖ ≤ M ∧ ∀ f : HalfEndPhysicalH2SourceGraph,
          ∃ F : E → ℝ, Continuous F ∧ ContDiffOn ℝ 2 F P ∧ F 0 = 0 ∧
            EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (T f))) F (closedBall (0:E) 4) ∧
            F =ᵐ[volume.restrict O]
              fullModelPhysicalField hκ0 hκ1 p f := by
  obtain ⟨G,C,K,F,hC,hK,hGAE,hF⟩ := exists_uniform_full_continuous_H4_family hκ0 hκ1
  let M := max K C.toReal
  have hM : 0 ≤ M := hK.trans (le_max_left _ _)
  refine ⟨M,hM,?_⟩
  intro p
  have hlin := continuous_full_completion_extension_linear hκ0 hκ1 p G hGAE (F p)
    (fun f => (hF p f).1) (fun f => (hF p f).2.2.2.1)
  let value (f : HalfEndPhysicalH2SourceGraph) : HalfEndEntranceValue :=
    ⟨fun x => F p f x,(hF p f).1.comp continuous_subtype_val⟩
  have heq (f : HalfEndPhysicalH2SourceGraph) (i : HalfEndPhysicalSliceIndex) :
      halfEndWeightedPhysicalSliceMap (value f) i =ᵐ[volume.restrict halfEndBasicAnnulus]
        weightedPhysicalDilation i.1 (F p f) := by
    filter_upwards [ae_restrict_mem halfEndBasicAnnulus_isOpen.measurableSet] with x hx
    exact halfEndWeightedPhysicalSliceMap_apply_in_ball (value f) i (le_of_lt hx.2)
  have hmem (f : HalfEndPhysicalH2SourceGraph) (i : HalfEndPhysicalSliceIndex) :
      MemWkp 4 2 (halfEndWeightedPhysicalSliceMap (value f) i) halfEndBasicAnnulus :=
    (MemWkp_congr_ae (by norm_num) halfEndBasicAnnulus_isOpen (heq f i)).mpr
      ((hF p f).2.2.2.2.2.1 i.1 i.2).1
  have hbound (f : HalfEndPhysicalH2SourceGraph) (i : HalfEndPhysicalSliceIndex) :
      (iteratedWeakSobolevNorm 4 2 (halfEndWeightedPhysicalSliceMap (value f) i) halfEndBasicAnnulus).toReal ≤ C.toReal*‖f‖ := by
    rw [wkpNorm_congr_ae (k := 4) (by norm_num) halfEndBasicAnnulus_isOpen (heq f i)]
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)
      ((hF p f).2.2.2.2.2.1 i.1 i.2).2
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg f)] using hh
  let S (f : HalfEndPhysicalH2SourceGraph) : HalfEndPhysicalH4Graph :=
    weakSobolevGraphOfBound halfEndBasicAnnulus halfEndBasicAnnulus_isOpen 4
      halfEndWeightedPhysicalSliceMap (value f) (hmem f) (C.toReal*‖f‖) (hbound f)
  have hSvalue (f : HalfEndPhysicalH2SourceGraph) : halfEndPhysicalH4GraphValue (S f) = value f := rfl
  have hSnorm (f : HalfEndPhysicalH2SourceGraph) : ‖S f‖ ≤ M*‖f‖ := by
    have hv : ‖value f‖ ≤ K*‖f‖ := by
      apply (ContinuousMap.norm_le (value f) (mul_nonneg hK (norm_nonneg f))).mpr
      intro x
      exact (hF p f).2.2.2.2.2.2 x x.2
    have hh := weakSobolevGraphOfBound_norm_le halfEndBasicAnnulus halfEndBasicAnnulus_isOpen 4
      halfEndWeightedPhysicalSliceMap (value f) (hmem f) (C.toReal*‖f‖)
      (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg f)) (hbound f)
    exact hh.trans (max_le (hv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg f)))
  let L : HalfEndPhysicalH2SourceGraph →ₗ[ℝ] HalfEndPhysicalH4Graph :=
    { toFun := S
      map_add' := by
        intro f g
        apply halfEndPhysicalH4GraphValue_injective
        rw [map_add,hSvalue,hSvalue,hSvalue]
        apply ContinuousMap.ext
        intro x
        exact congrFun (hlin.1 f g) x
      map_smul' := by
        intro c f
        apply halfEndPhysicalH4GraphValue_injective
        rw [map_smul,hSvalue,hSvalue]
        apply ContinuousMap.ext
        intro x
        exact congrFun (hlin.2 c f) x }
  let T := L.mkContinuous M hSnorm
  refine ⟨T,T.opNorm_le_bound hM hSnorm,?_⟩
  intro f
  refine ⟨F p f,(hF p f).1,(hF p f).2.1,(hF p f).2.2.1,?_,(hF p f).2.2.2.2.1⟩
  intro x hx
  change halfEndEntranceExtension (value f) x = F p f x
  exact halfEndEntranceExtension_of_mem (value f) hx

#print axioms exists_uniform_full_bounded_H4_solver
end Yamabe3.Analysis.UniformElliptic
