import Yamabe3.Analysis.BoundaryReflectionWeakDerivative

/-! A two-sided source may jump across the flat face. Its actual tangential
weak derivatives still have no boundary measure. No normal derivative of
the zero extension, or matching source trace, is asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem weakPartial_indicator_halfSpace_tangential
    {u g : E → ℝ} (i : Fin d) (hi : i ≠ 0)
    (hu : MemLp u 2 (volume.restrict (halfSpace d)))
    (hg : MemLp g 2 (volume.restrict (halfSpace d)))
    (hw : HasWeakPartialDeriv i g u (halfSpace d)) :
    HasWeakPartialDeriv i ((halfSpace d).indicator g)
      ((halfSpace d).indicator u) univ := by
  intro φ hφ hc _
  have ht := weakPartial_test_upToBoundary (by norm_num : (1:ℝ≥0∞)≤2)
    i hu hg hw hφ hc (fun h => (hi h).elim)
  simp only [Measure.restrict_univ]
  have he (v ψ : E → ℝ) :
      (∫ x, (halfSpace d).indicator v x * ψ x) = ∫ x in halfSpace d, v x * ψ x := by
    rw [← integral_indicator isOpen_halfSpace.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by by_cases hx : x∈halfSpace d <;> simp [hx]
  rw [he,he]
  exact ht

theorem weakPartial_reflectedSample_tangential
    {u g : E → ℝ} (i : Fin d) (hi : i ≠ 0)
    (hu : MemLp u 2 (volume.restrict (halfSpace d)))
    (hg : MemLp g 2 (volume.restrict (halfSpace d)))
    (hw : HasWeakPartialDeriv i g u (halfSpace d)) :
    HasWeakPartialDeriv i (reflectedSample 1 (by norm_num) g)
      (reflectedSample 1 (by norm_num) u) univ := by
  intro φ hφ hc _
  let ψ := fun x => φ ((scaledReflect (d:=d) 1 (by norm_num)).symm x)
  have hs : ContDiff ℝ ∞ ψ := hφ.comp (scaledReflect 1 (by norm_num)).symm.contDiff
  have hsc : HasCompactSupport ψ := hc.comp_homeomorph (scaledReflect 1 (by norm_num)).symm.toHomeomorph
  have ht := weakPartial_test_upToBoundary (by norm_num : (1:ℝ≥0∞)≤2)
    i hu hg hw hs hsc (fun h => (hi h).elim)
  simp only [Measure.restrict_univ]
  rw [integral_reflectedSample,integral_reflectedSample]
  simp only [inv_one,one_mul]
  refine Eq.trans ?_ ht
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [ψ]
    rw [reflected_test_partial_scaled 1 (by norm_num) hφ]
    simp [normalFactor,hi]

def twoSidedHalfSource (f g : E → ℝ) : E → ℝ :=
  (halfSpace d).indicator f + reflectedSample 1 (by norm_num) g

theorem memLp_twoSidedHalfSource {f g : E → ℝ}
    (hf : MemLp f 2 (volume.restrict (halfSpace d)))
    (hg : MemLp g 2 (volume.restrict (halfSpace d))) :
    MemLp (twoSidedHalfSource f g) 2 volume :=
  ((memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hf).add
    (memLp_reflectedSample 1 (by norm_num) hg)

theorem weakPartial_twoSidedHalfSource {f g df dg : E → ℝ}
    (i : Fin d) (hi : i ≠ 0)
    (hf : MemLp f 2 (volume.restrict (halfSpace d)))
    (hg : MemLp g 2 (volume.restrict (halfSpace d)))
    (hdf : MemLp df 2 (volume.restrict (halfSpace d)))
    (hdg : MemLp dg 2 (volume.restrict (halfSpace d)))
    (hwf : HasWeakPartialDeriv i df f (halfSpace d))
    (hwg : HasWeakPartialDeriv i dg g (halfSpace d)) :
    HasWeakPartialDeriv i (twoSidedHalfSource df dg) (twoSidedHalfSource f g) univ := by
  have h1 := weakPartial_indicator_halfSpace_tangential i hi hf hdf hwf
  have h2 := weakPartial_reflectedSample_tangential i hi hg hdg hwg
  intro φ hφ hc hs
  have hφL : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hDL : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)
  have hfI := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hf
  have hdfI := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hdf
  have hgR := memLp_reflectedSample 1 (by norm_num) hg
  have hdgR := memLp_reflectedSample 1 (by norm_num) hdg
  have hh1 := h1 φ hφ hc hs
  have hh2 := h2 φ hφ hc hs
  simp only [Measure.restrict_univ] at hh1 hh2 ⊢
  simp only [twoSidedHalfSource,Pi.add_apply,add_mul]
  have ha := integral_add (hfI.integrable_mul hDL) (hgR.integrable_mul hDL)
  have hb := integral_add (hdfI.integrable_mul hφL) (hdgR.integrable_mul hφL)
  simp only [Pi.mul_apply] at ha hb
  rw [ha,hb,hh1,hh2]
  ring

#print axioms weakPartial_indicator_halfSpace_tangential
#print axioms weakPartial_reflectedSample_tangential
#print axioms memLp_twoSidedHalfSource
#print axioms weakPartial_twoSidedHalfSource
end Yamabe3.Analysis.UniformElliptic
