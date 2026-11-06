import Yamabe3.Analysis.NativeHalfEndWeakLaplacian
import Yamabe3.Analysis.WeakLaplacianDilation
import Yamabe3.Analysis.NativeWeightedSourceBound
import Yamabe3.Analysis.DelaunayPhaseData

/-! The same field and same source under the actual exp(-s) dilation.
The equation has the shifted original orbit phase and the literal source
graph slice; no projected or renormalized replacement source is selected. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic.Iteration
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

def actualWeightedHalfEndField {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source) (s : ℝ) (x : E) : ℝ :=
  Real.exp (3*s/2) * cylinderLift
    (nativeHalfEndH2SourceJoint hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg f)
    (Real.exp (-s) • x)

theorem weighted_source_physical_identity (f : HalfEndPhysicalH2SourceGraph)
    (s : ℝ) {x : E} (hx : x ≠ 0) :
    Real.exp (3*s/2) * Real.exp (-s)^2 *
      (halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) (Real.exp (-s) • x)/8) =
        actualWeightedSourceSlice f s x := by
  have hn := norm_pos_iff.mpr hx
  unfold halfEndEuclideanPhysicalSource actualWeightedSourceSlice
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,
    radialScale_mul_positive (Real.exp_pos _) hn,radialScale_exp_neg]
  have he : Real.exp (3*s/2)*Real.exp (-s)^2*Real.exp (s/2) = 1 := by
    rw [pow_two,← mul_assoc,← Real.exp_add,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  calc
    _ = (Real.exp (3*s/2)*Real.exp (-s)^2*Real.exp (s/2)) *
        (radialScale ‖x‖ * halfEndSourceExtension (halfEndPhysicalH2SourceGraphValue f) (Real.exp (-s) • x)) := by ring
    _ = _ := by rw [he,one_mul]

theorem weighted_potential_identity {κ : ℝ} (p : DelaunayPhaseData κ)
    (s : ℝ) {x : E} (hx : x ≠ 0) :
    Real.exp (-s)^2 * nativeHalfEndPotentialCoefficient p.potential (Real.exp (-s) • x) =
      -annularDelaunayPotential p.orbit (p.phase+s) x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  unfold nativeHalfEndPotentialCoefficient
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.log_mul (Real.exp_pos _).ne' hn.ne',Real.log_exp]
  change Real.exp (-s)^2 * ((15/4)*p.orbit (-(-s+Real.log ‖x‖)+p.phase)^4 /
    (Real.exp (-s)*‖x‖)^2) = _
  have ht : -(-s+Real.log ‖x‖)+p.phase = (p.phase+s)-Real.log ‖x‖ := by ring
  rw [ht]
  unfold annularDelaunayPotential
  field_simp [(Real.exp_pos (-s)).ne',hn.ne']
  <;> ring

theorem nativeHalfEnd_weighted_weakNegativeLaplacian
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (p : DelaunayPhaseData κ)
    (f : HalfEndHighH2Source) (s : ℝ) {V : Set E} (hV : IsOpen V)
    (hVc : IsCompact (closure V))
    (hVO : ∀ x ∈ closure V, Real.exp (-s) • x ∈ O) :
    MemWkp 4 2 (actualWeightedHalfEndField hκ0 hκ1 p f s) V ∧
    weakNegativeLaplacian V (actualWeightedHalfEndField hκ0 hκ1 p f s) =ᵐ[volume.restrict V]
      (fun x => actualWeightedSourceSlice f.1 s x -
        annularDelaunayPotential p.orbit (p.phase+s) x*actualWeightedHalfEndField hκ0 hκ1 p f s x) := by
  let r := Real.exp (-s)
  have hr : r ≠ 0 := (Real.exp_pos (-s)).ne'
  let h : E ≃ₜ E := Homeomorph.smulOfNeZero r hr
  let W := h '' V
  have hW : IsOpen W := h.isOpenMap V hV
  have hWc : IsCompact (closure W) := by
    rw [show closure W = h '' closure V from (h.image_closure V).symm]
    exact hVc.image h.continuous
  have hWO : closure W ⊆ O := by
    rw [show closure W = h '' closure V from (h.image_closure V).symm]
    rintro _ ⟨x,hx,rfl⟩
    exact hVO x hx
  let u := cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg f)
  let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
  obtain ⟨hu,he⟩ := nativeHalfEndH2Source_weakNegativeLaplacian hκ0 hκ1 p.potential
    p.kernel_bound p.potential_nonneg p.potential_smooth f hW hWc hWO
  have hpre : (fun x : E => r • x) ⁻¹' W = V := by
    change h ⁻¹' (h '' V) = V
    exact h.injective.preimage_image V
  have hup := memWkp_comp_dilation hr hW (by norm_num) 4 hu
  rw [hpre] at hup
  have huc := MemWkp.const_smul (by norm_num : (1:ℝ≥0∞) ≤ 2) hV hup (Real.exp (3*s/2))
  refine ⟨huc,?_⟩
  have hd := weakNegativeLaplacian_comp_dilation hr hW (hu.le_of_le (by omega))
  have hd' := ae_comp_dilation hr he
  rw [hpre] at hd hd'
  have hm := weakNegativeLaplacian_const_mul hV (hup.le_of_le (by omega)) (Real.exp (3*s/2))
  filter_upwards [hm,hd,hd',ae_restrict_mem hV.measurableSet] with x hx hd hd' hxV
  have hx0 : x ≠ 0 := by
    intro hx0
    have hn := (hVO x (subset_closure hxV)).2
    apply hn
    simp [hx0]
  change weakNegativeLaplacian V (fun y => Real.exp (3*s/2)*u (r • y)) x = _ at hx
  change weakNegativeLaplacian V (fun y => Real.exp (3*s/2)*u (r • y)) x =
    actualWeightedSourceSlice f.1 s x - annularDelaunayPotential p.orbit (p.phase+s) x *
      (Real.exp (3*s/2)*u (r • x))
  rw [hx,hd,hd']
  have hs := weighted_source_physical_identity f.1 s hx0
  have hq := weighted_potential_identity p s hx0
  change Real.exp (3*s/2) * (r^2 * (F (r • x)/8+nativeHalfEndPotentialCoefficient p.potential (r • x)*u (r • x))) = _
  change Real.exp (3*s/2)*r^2*(F (r • x)/8) = _ at hs
  change r^2*nativeHalfEndPotentialCoefficient p.potential (r • x) = _ at hq
  change _ = actualWeightedSourceSlice f.1 s x -
    annularDelaunayPotential p.orbit (p.phase+s) x*(Real.exp (3*s/2)*u (r • x))
  rw [← hs]
  linear_combination Real.exp (3*s/2)*u (r • x)*hq

#print axioms weighted_source_physical_identity
#print axioms weighted_potential_identity
#print axioms nativeHalfEnd_weighted_weakNegativeLaplacian
end Yamabe3.Analysis.UniformElliptic
