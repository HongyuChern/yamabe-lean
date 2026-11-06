import Yamabe3.Analysis.NativePrincipalErrorValueBound
import Yamabe3.Analysis.C2DivergenceLinearity
import Yamabe3.Analysis.HalfEndGraphNorms

/-! Actual, arbitrarily small principal-error operator between the fixed
H4 solution and H2 source Banach graphs. Both norms include the retained
value coordinate; its construction is not assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_small_native_principal_error_graph_operator
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ, (g p).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ p ∈ Λ, (g p).pullbackVolumeDensity id 0 = 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ → ∀ p ∈ Λ,
      ∃ T : HalfEndPhysicalH4Graph →L[ℝ] HalfEndPhysicalH2SourceGraph,
        ‖T‖ ≤ τ ∧ ∀ (v : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance),
        halfEndPhysicalH2SourceGraphValue (T v) x = nativeNormalizedPrincipalError (g p) ε
          (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x := by
  obtain ⟨d,hd,hrows⟩ := exists_uniform_native_principal_error_rows Λ g hB hρ hτ
  obtain ⟨e,he,hvalues⟩ := exists_uniform_native_principal_error_value_bound Λ g hB hρ hτ
  refine ⟨min d e,lt_min hd he,?_⟩
  intro ε hε hsmall p hp
  have hεδ := hsmall.trans_le (min_le_left _ _)
  have hεe := hsmall.trans_le (min_le_right _ _)
  let H (v : HalfEndPhysicalH4Graph) (x : E) := nativeNormalizedPrincipalError (g p) ε
    (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x
  let value (v : HalfEndPhysicalH4Graph) : HalfEndSourceValue :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => H v x)
      (nativeNormalizedPrincipalError_entrance_continuous (g p) ε v)
      (τ*‖v‖) (hvalues ε hε hεe p hp v)
  have hval (v : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance) : value v x = H v x := rfl
  have hroweq (v : HalfEndPhysicalH4Graph) (i : HalfEndPhysicalSliceIndex) :
      halfEndWeightedSourceSliceMap (value v) i =ᵐ[volume.restrict halfEndSourceAnnulus]
        fun x => radialScale ‖x‖ * H v (Real.exp (-i.1) • x) := by
    filter_upwards [ae_restrict_mem halfEndSourceAnnulus_isOpen.measurableSet] with x hx
    rw [halfEndWeightedSourceSliceMap_apply_in_ball (value v) i
      (norm_pos_iff.mp (by linarith [hx.1])) hx.2.le]
    rfl
  have hmem (v : HalfEndPhysicalH4Graph) (i : HalfEndPhysicalSliceIndex) :
      MemWkp 2 2 (halfEndWeightedSourceSliceMap (value v) i) halfEndSourceAnnulus :=
    (MemWkp_congr_ae (by norm_num) halfEndSourceAnnulus_isOpen (hroweq v i)).mpr
      (hrows ε hε hεδ p hp v i).1
  have hnorm (v : HalfEndPhysicalH4Graph) (i : HalfEndPhysicalSliceIndex) :
      (iteratedWeakSobolevNorm 2 2 (halfEndWeightedSourceSliceMap (value v) i) halfEndSourceAnnulus).toReal ≤ τ*‖v‖ := by
    rw [wkpNorm_congr_ae (k := 2) (by norm_num) halfEndSourceAnnulus_isOpen (hroweq v i)]
    have hh := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal τ*ENNReal.ofReal ‖v‖ ≠ ⊤)
      (hrows ε hε hεδ p hp v i).2
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hτ.le,ENNReal.toReal_ofReal (norm_nonneg v)] using hh
  let S (v : HalfEndPhysicalH4Graph) : HalfEndPhysicalH2SourceGraph :=
    weakSobolevGraphOfBound halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
      halfEndWeightedSourceSliceMap (value v) (hmem v) (τ*‖v‖) (hnorm v)
  have hSvalue (v) : halfEndPhysicalH2SourceGraphValue (S v) = value v := rfl
  have hSnorm (v) : ‖S v‖ ≤ τ*‖v‖ := by
    have hv : ‖value v‖ ≤ τ*‖v‖ :=
      (BoundedContinuousFunction.norm_le (mul_nonneg hτ.le (norm_nonneg v))).mpr (hvalues ε hε hεe p hp v)
    exact (weakSobolevGraphOfBound_norm_le halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
      halfEndWeightedSourceSliceMap (value v) (hmem v) (τ*‖v‖)
      (mul_nonneg hτ.le (norm_nonneg v)) (hnorm v)).trans (max_le hv le_rfl)
  let L : HalfEndPhysicalH4Graph →ₗ[ℝ] HalfEndPhysicalH2SourceGraph :=
    { toFun := S
      map_add' := by
        intro v w
        apply halfEndPhysicalH2SourceGraphValue_injective
        rw [map_add,hSvalue,hSvalue,hSvalue]
        apply BoundedContinuousFunction.ext
        intro x
        exact nativeNormalizedPrincipalError_graph_add (g p) ε v w x
      map_smul' := by
        intro c v
        apply halfEndPhysicalH2SourceGraphValue_injective
        rw [map_smul,hSvalue,hSvalue]
        apply BoundedContinuousFunction.ext
        intro x
        exact nativeNormalizedPrincipalError_graph_smul (g p) ε c v x }
  let T := L.mkContinuous τ hSnorm
  exact ⟨T,LinearMap.mkContinuous_norm_le _ hτ.le _,fun v x => rfl⟩

#print axioms exists_small_native_principal_error_graph_operator
end Yamabe3.Analysis.UniformElliptic
