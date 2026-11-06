import Yamabe3.Analysis.UniformElliptic.HalfEndPhysicalH4Graph
import Yamabe3.Analysis.Green.NativeLocalParametrix
import Yamabe3.Analysis.NativeJacobianAnnularSobolev

/-!
# An actual weighted weak H2 graph for the physical half-end source

The entrance value is a bounded continuous function on the punctured
closed ball of radius three. The source slices use the fixed annulus
3/4 < norm z < 3/2. The solution graph retains its larger radius-four
entrance and 1/2 < norm z < 2 annulus, leaving a fixed margin for actual
whole-source-norm estimates. Its radial weight is retained: the physical source may grow
like r^(-1/2) and need not have a limit at the puncture. For the same native
density rho, reconstruction includes the exact factor 8 a(epsilon)/epsilon^2.

The proved identity is
  exp(2s) [r^2 rho(r z) F(r z)/(8 a(r))]
    = a(norm z) h(exp(-s) z),  r=epsilon exp(-s).
Thus the complete graph stores actual weak H2 jets of the literal source
used by the scaled native equation. It does not supply an inverse or a
source transport to the original manifold without its chart identity.
In particular, source data on this radius-three collar do not produce
a solution extension on the radius-four negative-time collar: the
global inverse must construct that actual bounded entrance lifting.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ENNReal BoundedContinuousFunction

namespace Yamabe3.Analysis.UniformElliptic

open Delaunay GreenParametrix
open Poincare.Analysis.Sobolev.Euclidean

local notation "E3" => EuclideanSpace ℝ (Fin 3)

abbrev halfEndSourceAnnulus : Set E3 := NativeJacobianAnnulus.sourceAnnulus

theorem halfEndSourceAnnulus_isOpen : IsOpen halfEndSourceAnnulus :=
  NativeJacobianAnnulus.sourceAnnulus_open

abbrev HalfEndSourceEntrance := {x : E3 // x ≠ 0 ∧ ‖x‖ ≤ 3}
abbrev HalfEndSourceValue := HalfEndSourceEntrance →ᵇ ℝ

def halfEndSourceEval (x : E3) : HalfEndSourceValue →L[ℝ] ℝ := by
  classical
  exact if hx : x ≠ 0 ∧ ‖x‖ ≤ 3 then
    BoundedContinuousFunction.evalCLM (𝕜 := ℝ) (⟨x, hx⟩ : HalfEndSourceEntrance) else 0

def halfEndSourceExtension (f : HalfEndSourceValue) (x : E3) : ℝ :=
  halfEndSourceEval x f

theorem halfEndSourceExtension_of_mem (f : HalfEndSourceValue)
    {x : E3} (hx : x ≠ 0 ∧ ‖x‖ ≤ 3) :
    halfEndSourceExtension f x = f ⟨x, hx⟩ := by
  classical
  simp [halfEndSourceExtension, halfEndSourceEval, hx]

@[simp] theorem halfEndSourceExtension_zero (f : HalfEndSourceValue) :
    halfEndSourceExtension f (0 : E3) = 0 := by
  classical
  simp [halfEndSourceExtension, halfEndSourceEval]

@[simp] theorem halfEndSourceExtension_add (f h : HalfEndSourceValue) (x : E3) :
    halfEndSourceExtension (f + h) x =
      halfEndSourceExtension f x + halfEndSourceExtension h x :=
  map_add (halfEndSourceEval x) f h

@[simp] theorem halfEndSourceExtension_smul (c : ℝ) (f : HalfEndSourceValue) (x : E3) :
    halfEndSourceExtension (c • f) x = c * halfEndSourceExtension f x :=
  map_smul (halfEndSourceEval x) c f

@[simp] theorem halfEndSourceExtension_sub (f h : HalfEndSourceValue) (x : E3) :
    halfEndSourceExtension (f - h) x =
      halfEndSourceExtension f x - halfEndSourceExtension h x :=
  map_sub (halfEndSourceEval x) f h

/-- The literal physical source, with the same native density and the
exact coefficient eight. The value at the puncture is only a convention. -/
def nativeHalfEndSourceRealization (g : RiemannianMetric 3 E3) (ε : ℝ)
    (f : HalfEndSourceValue) (x : E3) : ℝ :=
  (8 * radialScale ε / ε ^ 2) * radialScale ‖ε⁻¹ • x‖ *
    halfEndSourceExtension f (ε⁻¹ • x) / g.pullbackVolumeDensity id x

/-- The exact source normalization already used by the physical native
Jacobian and scalar-six residual, now for an arbitrary same source F. -/
def nativeHalfEndNormalizedSource (g : RiemannianMetric 3 E3) (ε : ℝ)
    (F : E3 → ℝ) (s : ℝ) (z : E3) : ℝ :=
  let r := ε * Real.exp (-s)
  (r ^ 2 * g.pullbackVolumeDensity id (r • z) / (8 * radialScale r)) * F (r • z)

def halfEndWeightedSourceSliceMap :
    HalfEndSourceValue →ₗ[ℝ] (HalfEndPhysicalSliceIndex → E3 → ℝ) where
  toFun f i z := radialScale ‖z‖ * halfEndSourceExtension f (Real.exp (-i.1) • z)
  map_add' f h := by
    funext i z
    simp only [Pi.add_apply, halfEndSourceExtension_add]
    ring
  map_smul' c f := by
    funext i z
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, halfEndSourceExtension_smul]
    ring

theorem halfEndWeightedSourceSliceMap_continuous
    (i : HalfEndPhysicalSliceIndex) (z : E3) :
    Continuous (fun f : HalfEndSourceValue => halfEndWeightedSourceSliceMap f i z) :=
  continuous_const.mul (halfEndSourceEval (Real.exp (-i.1) • z)).continuous

theorem halfEnd_source_slice_mem_entrance (i : HalfEndPhysicalSliceIndex)
    {z : E3} (hz : z ≠ 0) (hz2 : ‖z‖ ≤ 3 / 2) :
    Real.exp (-i.1) • z ≠ 0 ∧ ‖Real.exp (-i.1) • z‖ ≤ 3 := by
  refine ⟨smul_ne_zero (Real.exp_pos _).ne' hz, ?_⟩
  have he : Real.exp (-i.1) ≤ 2 := by
    have h := Real.exp_le_exp.mpr (show -i.1 ≤ Real.log 2 by linarith [i.2])
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (-i.1) * ‖z‖ ≤ 2 * ‖z‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg z)
    _ ≤ 3 := by linarith

theorem halfEndWeightedSourceSliceMap_apply_in_ball
    (f : HalfEndSourceValue) (i : HalfEndPhysicalSliceIndex) {z : E3}
    (hz : z ≠ 0) (hz2 : ‖z‖ ≤ 3 / 2) :
    halfEndWeightedSourceSliceMap f i z = radialScale ‖z‖ *
      f ⟨Real.exp (-i.1) • z, halfEnd_source_slice_mem_entrance i hz hz2⟩ := by
  change radialScale ‖z‖ * halfEndSourceExtension f (Real.exp (-i.1) • z) = _
  rw [halfEndSourceExtension_of_mem f (halfEnd_source_slice_mem_entrance i hz hz2)]

private theorem nativeHalfEndNormalizedSource_realization_nonzero
    (g : RiemannianMetric 3 E3) {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndSourceValue) (i : HalfEndPhysicalSliceIndex) {z : E3} (hz : z ≠ 0) :
    nativeHalfEndNormalizedSource g ε (nativeHalfEndSourceRealization g ε f) i.1 z =
      Real.exp (-i.1) ^ 2 * halfEndWeightedSourceSliceMap f i z := by
  have ha : 0 < Real.exp (-i.1) := Real.exp_pos _
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcoord : ε⁻¹ • ((ε * Real.exp (-i.1)) • z) = Real.exp (-i.1) • z := by
    rw [smul_smul, inv_mul_cancel_left₀ hε.ne']
  have hρ : g.pullbackVolumeDensity id ((ε * Real.exp (-i.1)) • z) ≠ 0 :=
    ((native_density_smooth_positive g).2 _).ne'
  change ((ε * Real.exp (-i.1)) ^ 2 *
      g.pullbackVolumeDensity id ((ε * Real.exp (-i.1)) • z) /
        (8 * radialScale (ε * Real.exp (-i.1)))) *
      ((8 * radialScale ε / ε ^ 2) *
        radialScale ‖ε⁻¹ • ((ε * Real.exp (-i.1)) • z)‖ *
          halfEndSourceExtension f (ε⁻¹ • ((ε * Real.exp (-i.1)) • z)) /
            g.pullbackVolumeDensity id ((ε * Real.exp (-i.1)) • z)) =
    Real.exp (-i.1) ^ 2 *
      (radialScale ‖z‖ * halfEndSourceExtension f (Real.exp (-i.1) • z))
  rw [hcoord, norm_smul, Real.norm_of_nonneg ha.le,
    radialScale_mul_positive hε ha, radialScale_mul_positive ha hn]
  field_simp [hε.ne', hρ, (radialScale_pos ε).ne',
    (radialScale_pos (Real.exp (-i.1))).ne']
  <;> ring

/-- The completed source graph uses exactly the weighted physical source
of the native equation, including its actual Jacobian density. -/
theorem halfEndWeightedSourceSliceMap_eq_physical
    (g : RiemannianMetric 3 E3) {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndSourceValue) (i : HalfEndPhysicalSliceIndex) (z : E3) :
    halfEndWeightedSourceSliceMap f i z = Real.exp (2 * i.1) *
      nativeHalfEndNormalizedSource g ε (nativeHalfEndSourceRealization g ε f) i.1 z := by
  by_cases hz : z = 0
  · subst z
    simp [halfEndWeightedSourceSliceMap, nativeHalfEndNormalizedSource,
      nativeHalfEndSourceRealization]
  · rw [nativeHalfEndNormalizedSource_realization_nonzero g hε f i hz]
    have he : Real.exp (2 * i.1) * Real.exp (-i.1) ^ 2 = 1 := by
      rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [← mul_assoc, he, one_mul]

/-- The entrance normalization identifies the reconstructed source with
the original F at every actual physical point of the punctured collar. -/
theorem nativeHalfEndSourceRealization_eq_same_source
    (g : RiemannianMetric 3 E3) {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndSourceValue) (F : E3 → ℝ)
    (hF : ∀ y : HalfEndSourceEntrance,
      radialScale ‖(y : E3)‖ * f y =
        (ε ^ 2 * g.pullbackVolumeDensity id (ε • (y : E3)) / (8 * radialScale ε)) *
          F (ε • (y : E3))) (y : HalfEndSourceEntrance) :
    nativeHalfEndSourceRealization g ε f (ε • (y : E3)) = F (ε • (y : E3)) := by
  have hρ : g.pullbackVolumeDensity id (ε • (y : E3)) ≠ 0 :=
    ((native_density_smooth_positive g).2 _).ne'
  unfold nativeHalfEndSourceRealization
  rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul,
    halfEndSourceExtension_of_mem f y.2]
  rw [mul_assoc, hF y]
  field_simp [hε.ne', hρ, (radialScale_pos ε).ne']
  <;> ring

abbrev HalfEndPhysicalH2SourceGraph :=
  weakSobolevGraph halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
    halfEndWeightedSourceSliceMap

instance halfEndPhysicalH2SourceGraphCompleteSpace : CompleteSpace HalfEndPhysicalH2SourceGraph :=
  weakSobolevGraph_completeSpace halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
    halfEndWeightedSourceSliceMap halfEndWeightedSourceSliceMap_continuous

def halfEndPhysicalH2SourceGraphValue : HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndSourceValue :=
  weakSobolevGraphValue halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
    halfEndWeightedSourceSliceMap

theorem halfEndPhysicalH2SourceGraphValue_injective :
    Function.Injective halfEndPhysicalH2SourceGraphValue :=
  weakSobolevGraph_fst_injective halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
    halfEndWeightedSourceSliceMap

/-- Actual source membership and the full weighted weak H2 bound hold for
the very same reconstructed F in every legal slice. -/
theorem halfEndPhysicalH2SourceGraph_actual_weighted_bound
    (g : RiemannianMetric 3 E3) {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndPhysicalH2SourceGraph) (s : ℝ) (hs : -(Real.log 2) ≤ s) :
    let F := nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue f)
    MemWkp 2 2 (nativeHalfEndNormalizedSource g ε F s) halfEndSourceAnnulus ∧
      ENNReal.ofReal (Real.exp (2 * s)) * iteratedWeakSobolevNorm 2 2
        (nativeHalfEndNormalizedSource g ε F s) halfEndSourceAnnulus ≤ ENNReal.ofReal ‖f‖ := by
  let i : HalfEndPhysicalSliceIndex := ⟨s, hs⟩
  let F := nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue f)
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have heq : halfEndWeightedSourceSliceMap f.1.1 i = fun z =>
      Real.exp (2 * s) * nativeHalfEndNormalizedSource g ε F s z := by
    funext z
    exact halfEndWeightedSourceSliceMap_eq_physical g hε f.1.1 i z
  have hweighted := (f.2 i).1
  have hfinite := (wkpNorm_lt_top_of_memWkp hweighted).ne
  have hbound : iteratedWeakSobolevNorm 2 2
      (halfEndWeightedSourceSliceMap f.1.1 i) halfEndSourceAnnulus ≤ ENNReal.ofReal ‖f‖ :=
    (ENNReal.le_ofReal_iff_toReal_le hfinite (norm_nonneg f)).mpr
      (weakSobolevGraph_local_norm_le halfEndSourceAnnulus halfEndSourceAnnulus_isOpen 2
        halfEndWeightedSourceSliceMap f i)
  rw [heq] at hweighted
  have hu := MemWkp.const_smul hp halfEndSourceAnnulus_isOpen hweighted
    (Real.exp (2 * s))⁻¹
  have hundo : (fun z => (Real.exp (2 * s))⁻¹ *
      (Real.exp (2 * s) * nativeHalfEndNormalizedSource g ε F s z)) =
        nativeHalfEndNormalizedSource g ε F s := by
    funext z
    rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
  rw [hundo] at hu
  refine ⟨hu, ?_⟩
  rw [heq, wkpNorm_const_smul hp halfEndSourceAnnulus_isOpen hu,
    Real.enorm_eq_ofReal (Real.exp_pos _).le] at hbound
  exact hbound

/-- Graph convergence is convergence of the same literal physical source
at every fixed coordinate point, with its true metric and scale. -/
theorem halfEndPhysicalH2SourceGraph_same_source_pointwise_limit
    (g : RiemannianMetric 3 E3) (ε : ℝ)
    {f : ℕ → HalfEndPhysicalH2SourceGraph} {F : HalfEndPhysicalH2SourceGraph}
    (hF : Tendsto f atTop (𝓝 F)) (x : E3) :
    Tendsto (fun n => nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue (f n)) x)
      atTop (𝓝 (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue F) x)) := by
  have h : Continuous (fun z : HalfEndPhysicalH2SourceGraph =>
      nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue z) x) :=
    (continuous_const.mul ((halfEndSourceEval (ε⁻¹ • x)).continuous.comp
      halfEndPhysicalH2SourceGraphValue.continuous)).div_const _
  exact h.continuousAt.tendsto.comp hF

/-- A graph difference controls one supremum over all legal source
slices. This is strong convergence in the complete weighted weak H2
source quantity, for the same physical sources and the same density. -/
theorem halfEndPhysicalH2SourceGraph_uniform_weak_h2_convergence
    (g : RiemannianMetric 3 E3) {ε : ℝ} (hε : 0 < ε)
    {f : ℕ → HalfEndPhysicalH2SourceGraph} {F : HalfEndPhysicalH2SourceGraph}
    (hF : Tendsto f atTop (𝓝 F)) :
    Tendsto (fun n => ⨆ s : ℝ, ⨆ (_hs : -(Real.log 2) ≤ s),
      ENNReal.ofReal (Real.exp (2 * s)) * iteratedWeakSobolevNorm 2 2
        (fun z => nativeHalfEndNormalizedSource g ε
          (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue (f n))) s z -
          nativeHalfEndNormalizedSource g ε
            (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue F)) s z)
        halfEndSourceAnnulus) atTop (𝓝 0) := by
  have hsub (n : ℕ) (s : ℝ) :
      nativeHalfEndNormalizedSource g ε
        (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue (f n - F))) s =
      fun z => nativeHalfEndNormalizedSource g ε
        (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue (f n))) s z -
          nativeHalfEndNormalizedSource g ε
            (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue F)) s z := by
    funext z
    have hval : halfEndPhysicalH2SourceGraphValue (f n - F) =
        halfEndPhysicalH2SourceGraphValue (f n) - halfEndPhysicalH2SourceGraphValue F := rfl
    rw [hval]
    simp only [nativeHalfEndNormalizedSource, nativeHalfEndSourceRealization,
      halfEndSourceExtension_sub]
    ring
  have hb (n : ℕ) : (⨆ s : ℝ, ⨆ (_hs : -(Real.log 2) ≤ s),
      ENNReal.ofReal (Real.exp (2 * s)) * iteratedWeakSobolevNorm 2 2
        (fun z => nativeHalfEndNormalizedSource g ε
          (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue (f n))) s z -
          nativeHalfEndNormalizedSource g ε
            (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue F)) s z)
        halfEndSourceAnnulus) ≤ ENNReal.ofReal ‖f n - F‖ := by
    refine iSup_le fun s => iSup_le fun hs => ?_
    have h := (halfEndPhysicalH2SourceGraph_actual_weighted_bound g hε (f n - F) s hs).2
    change ENNReal.ofReal (Real.exp (2 * s)) * iteratedWeakSobolevNorm 2 2
      (nativeHalfEndNormalizedSource g ε
        (nativeHalfEndSourceRealization g ε (halfEndPhysicalH2SourceGraphValue (f n - F))) s)
      halfEndSourceAnnulus ≤ ENNReal.ofReal ‖f n - F‖ at h
    rw [hsub n s] at h
    exact h
  have hn : Tendsto (fun n => ‖f n - F‖) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => F) atTop (𝓝 F) := tendsto_const_nhds
    have hd : Tendsto (fun n => dist (f n) F) atTop (𝓝 0) := by
      simpa only [dist_self] using hF.dist hconst
    change Tendsto (fun n => dist (f n).1 F.1) atTop (𝓝 0) at hd
    change Tendsto (fun n => ‖(f n).1 - F.1‖) atTop (𝓝 0)
    simpa only [dist_eq_norm] using hd
  have hne : Tendsto (fun n => ENNReal.ofReal ‖f n - F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hn
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hne δ hδ
  exact ⟨N, fun n hn => (hb n).trans (hN n hn)⟩

#print axioms halfEndWeightedSourceSliceMap_eq_physical
#print axioms nativeHalfEndSourceRealization_eq_same_source
#print axioms halfEndPhysicalH2SourceGraphCompleteSpace
#print axioms halfEndPhysicalH2SourceGraphValue_injective
#print axioms halfEndPhysicalH2SourceGraph_actual_weighted_bound
#print axioms halfEndPhysicalH2SourceGraph_same_source_pointwise_limit
#print axioms halfEndPhysicalH2SourceGraph_uniform_weak_h2_convergence

end Yamabe3.Analysis.UniformElliptic
