import Yamabe3.Analysis.SobolevEuclideanChart
import Yamabe3.Analysis.NativeHalfEndSourceRegularity

/-! The original half-end graph source has actual H2 across the entrance
annulus, and hence in every fixed compact sphere-flattening chart there.
The exact physical factor eight and the actual volume density are retained.
No coordinate H2 premise is added to the source graph. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- A full annulus containing the unit sphere, not only the punctured ball.
Both actual weak H2 and a homogeneous graph norm bound are produced. -/
theorem halfEndH2SourceGraph_entrance_H2_bound (f : HalfEndPhysicalH2SourceGraph) :
    MemWkp 2 2 (halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f)) halfEndSourceAnnulus ∧
    iteratedWeakSobolevNorm 2 2 (halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f))
      halfEndSourceAnnulus ≤ 8 * ENNReal.ofReal ‖f‖ := by
  let i : HalfEndPhysicalSliceIndex := ⟨0, neg_nonpos.mpr (Real.log_nonneg (by norm_num))⟩
  have hm := (f.2 i).1
  have hn : iteratedWeakSobolevNorm 2 2 (halfEndWeightedSourceSliceMap f.1.1 i) halfEndSourceAnnulus ≤
      ENNReal.ofReal ‖f‖ :=
    (ENNReal.le_ofReal_iff_toReal_le (wkpNorm_lt_top_of_memWkp hm).ne (norm_nonneg f)).mpr
      (weakSobolevGraph_local_norm_le halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
        halfEndWeightedSourceSliceMap f i)
  have heq : (fun x => (8 : ℝ) * halfEndWeightedSourceSliceMap f.1.1 i x) =
      halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) := by
    funext x
    change 8 * (Delaunay.radialScale ‖x‖ * halfEndSourceExtension f.1.1 (Real.exp (-0) • x)) =
      8 * Delaunay.radialScale ‖x‖ * halfEndSourceExtension f.1.1 x
    simp only [neg_zero, Real.exp_zero, one_smul]
    ring
  refine ⟨heq ▸ MemWkp.const_smul (by norm_num) halfEndSourceAnnulus_isOpen hm 8, ?_⟩
  rw [← heq, wkpNorm_const_smul (by norm_num) halfEndSourceAnnulus_isOpen hm]
  norm_num only [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat]
  exact mul_le_mul le_rfl hn zero_le zero_le

/-- Same physical graph input, actual chart, actual Jacobian density.
The finite bound is chosen before the source. -/
theorem exists_halfEndH2_source_chart_bound
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOs : closure O ⊆ e.source) (heW : e '' closure O ⊆ halfEndSourceAnnulus) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : HalfEndPhysicalH2SourceGraph,
      MemWkp 2 2
        (fun x => (RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity e x *
          halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) (e x)) O ∧
      iteratedWeakSobolevNorm 2 2
        (fun x => (RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity e x *
          halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) (e x)) O ≤
        C * ENNReal.ofReal ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_euclidean_chart_density_source_bound 2 e he hei hO hOc hOs
    halfEndSourceAnnulus_isOpen heW
  refine ⟨C*8, by finiteness, ?_⟩
  intro f
  have hf := halfEndH2SourceGraph_entrance_H2_bound f
  have hh := hb _ hf.1
  refine ⟨hh.1, ?_⟩
  exact hh.2.trans (by simpa only [mul_assoc] using mul_le_mul le_rfl hf.2 zero_le zero_le)

#print axioms halfEndH2SourceGraph_entrance_H2_bound
#print axioms exists_halfEndH2_source_chart_bound
end Yamabe3.Analysis.UniformElliptic
