import Yamabe3.Analysis.NativeAffinePrincipalSource

/-! Actual native principal-error closure on a complete common space
retaining the four regular low jets AND the decaying H4 field. The two
pieces form ONE field in the differential expression. This does not yet
include the scalar/potential defect or prove a total feedback inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter Metric MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
local notation "E3" => EuclideanSpace ℝ (Fin 3)
abbrev RegularLowH4Space := RegularLowJet × HalfEndPhysicalH4Graph

def regularLowH4Field (z:RegularLowH4Space) (x:E3) : ℝ :=
  regularAffineField z.1 x+halfEndEntranceExtension (halfEndPhysicalH4GraphValue z.2) x

theorem regularLowH4Space_complete : CompleteSpace RegularLowH4Space := inferInstance

theorem exists_small_native_regular_H4_principal_source
    {ι:Type*} (Λ:Finset ι) (g:ι→RiemannianMetric 3 E3)
    (hB:∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ:∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) {τ:ℝ} (hτ:0<τ) :
    ∃δ:ℝ,0<δ ∧ ∀ε:ℝ,0≤ε → ε<δ → ∀p∈Λ,
      ∃T:RegularLowH4Space →L[ℝ] HalfEndPhysicalH2SourceGraph,‖T‖≤τ ∧
        ∀z:RegularLowH4Space,∀x:HalfEndSourceEntrance,
          halfEndPhysicalH2SourceGraphValue (T z) x=
            nativeNormalizedPrincipalError (g p) ε (regularLowH4Field z) x := by
  obtain ⟨δ₁,hδ₁,hAff⟩ := exists_small_native_affine_principal_source Λ g hB hρ (half_pos hτ)
  obtain ⟨δ₂,hδ₂,hH4⟩ := exists_small_native_principal_error_graph_operator Λ g hB hρ (half_pos hτ)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,fun ε hε hεδ p hp => ?_⟩
  obtain ⟨A,hA,hAv⟩ := hAff ε hε (hεδ.trans_le (min_le_left _ _)) p hp
  obtain ⟨P,hP,hPv⟩ := hH4 ε hε (hεδ.trans_le (min_le_right _ _)) p hp
  let L := A.comp (ContinuousLinearMap.fst ℝ RegularLowJet HalfEndPhysicalH4Graph)+
    P.comp (ContinuousLinearMap.snd ℝ RegularLowJet HalfEndPhysicalH4Graph)
  have hbound (z:RegularLowH4Space) : ‖L z‖≤τ*‖z‖ := by
    change ‖A z.1+P z.2‖≤_
    apply (norm_add_le _ _).trans
    have ha : ‖A z.1‖≤(τ/2)*‖z‖ :=
      (A.le_opNorm z.1).trans (mul_le_mul hA (norm_fst_le z) (norm_nonneg _) (half_pos hτ).le)
    have hp : ‖P z.2‖≤(τ/2)*‖z‖ :=
      (P.le_opNorm z.2).trans (mul_le_mul hP (norm_snd_le z) (norm_nonneg _) (half_pos hτ).le)
    linarith
  refine ⟨L,L.opNorm_le_bound hτ.le hbound,fun z x => ?_⟩
  change halfEndPhysicalH2SourceGraphValue (A z.1+P z.2) x=_
  rw [map_add]
  change halfEndPhysicalH2SourceGraphValue (A z.1) x+halfEndPhysicalH2SourceGraphValue (P z.2) x=_
  rw [hAv,hPv]
  have hx : (x:E3)∈ball (0:E3) 4\{(0:E3)} :=
    ⟨by rw [mem_ball_zero_iff];linarith [x.2.2],x.2.1⟩
  unfold nativeNormalizedPrincipalError nativePrincipalError regularLowH4Field
  rw [principalSource_add_C2On (a:=fun y => nativeDivergenceMatrix (g p) (ε • y)-1)
    (contDiff_nativeScaledPrincipalError (g p) ε) (isOpen_ball.sdiff isClosed_singleton)
    ((regularAffineField_smooth z.1).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn
    (halfEndPhysicalH4Graph_contDiffOn_two z.2) hx]
  ring

#print axioms regularLowH4Space_complete
#print axioms exists_small_native_regular_H4_principal_source
end Yamabe3.Analysis.UniformElliptic
