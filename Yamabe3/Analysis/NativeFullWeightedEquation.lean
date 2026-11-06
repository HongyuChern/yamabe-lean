import Yamabe3.Analysis.NativeFullWeakLaplacian
import Yamabe3.Analysis.NativeWeightedEquation
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

def actualWeightedFullModelField {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (p : DelaunayPhaseData κ) (f : HalfEndPhysicalH2SourceGraph) (s : ℝ) (x : E) : ℝ :=
  Real.exp (3*s/2)*fullModelPhysicalField hκ0 hκ1 p f (Real.exp (-s) • x)

theorem fullModel_weighted_weakNegativeLaplacian
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (p : DelaunayPhaseData κ)
    (f : HalfEndPhysicalH2SourceGraph) (s : ℝ) {V : Set E} (hV : IsOpen V)
    (hVc : IsCompact (closure V))
    (hVO : ∀ x ∈ closure V, Real.exp (-s) • x ∈ O) :
    MemWkp 4 2 (actualWeightedFullModelField hκ0 hκ1 p f s) V ∧
    weakNegativeLaplacian V (actualWeightedFullModelField hκ0 hκ1 p f s) =ᵐ[volume.restrict V]
      (fun x => actualWeightedSourceSlice f s x -
        annularDelaunayPotential p.orbit (p.phase+s) x*actualWeightedFullModelField hκ0 hκ1 p f s x) := by
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
  let u := fullModelPhysicalField hκ0 hκ1 p f
  let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f)
  obtain ⟨hu,he⟩ := fullModelPhysicalField_weakNegativeLaplacian hκ0 hκ1 p f hW hWc hWO
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
    actualWeightedSourceSlice f s x - annularDelaunayPotential p.orbit (p.phase+s) x *
      (Real.exp (3*s/2)*u (r • x))
  rw [hx,hd,hd']
  have hs := weighted_source_physical_identity f s hx0
  have hq := weighted_potential_identity p s hx0
  change Real.exp (3*s/2) * (r^2 * (F (r • x)/8+nativeHalfEndPotentialCoefficient p.potential (r • x)*u (r • x))) = _
  change Real.exp (3*s/2)*r^2*(F (r • x)/8) = _ at hs
  change r^2*nativeHalfEndPotentialCoefficient p.potential (r • x) = _ at hq
  change _ = actualWeightedSourceSlice f s x -
    annularDelaunayPotential p.orbit (p.phase+s) x*(Real.exp (3*s/2)*u (r • x))
  rw [← hs]
  linear_combination Real.exp (3*s/2)*u (r • x)*hq

#print axioms fullModel_weighted_weakNegativeLaplacian
end Yamabe3.Analysis.UniformElliptic
