import Yamabe3.Analysis.UniformElliptic.WeakSobolevGraphSpace
import Yamabe3.Analysis.UniformElliptic.HalfEndAnnularComparison
import Mathlib.Topology.ContinuousMap.Compact

/-!
# A complete weak H4 graph of one physical half-end correction

The value coordinate is an actual continuous entrance-normalized function
on the closed ball of radius four. The graph rows are its literal weighted
physical dilations on the basic annulus, for s >= -log 2. Their derivatives
are the actual weak L2 coordinate jets, with the full finite sum norm.

The value-coordinate norm is retained in the graph norm. No estimate which
removes it, no smooth density assertion, and no smoothness of the zero
extension across the outer sphere is presumed. The zero extension is only
a total-function convention; all declared annular evaluations stay inside
the closed ball. The same physical function is recovered at every scale.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Delaunay
open Poincare.Analysis.Sobolev.Euclidean

local notation "E3" => EuclideanSpace ℝ (Fin 3)

abbrev HalfEndEntranceBall := closedBall (0 : E3) 4

instance halfEndEntranceBallCompactSpace : CompactSpace HalfEndEntranceBall :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E3) 4)

abbrev HalfEndEntranceValue := C(HalfEndEntranceBall, ℝ)
abbrev HalfEndPhysicalSliceIndex := {s : ℝ // -(Real.log 2) ≤ s}

/-- Evaluation of the entrance value, extended by zero solely to make a
total function on Euclidean space. Each fixed evaluation is continuous. -/
def halfEndEntranceEval (x : E3) : HalfEndEntranceValue →L[ℝ] ℝ := by
  classical
  exact if hx : x ∈ closedBall (0 : E3) 4 then
    ContinuousMap.evalCLM (R := ℝ) (⟨x, hx⟩ : HalfEndEntranceBall) else 0

def halfEndEntranceExtension (f : HalfEndEntranceValue) (x : E3) : ℝ :=
  halfEndEntranceEval x f

theorem halfEndEntranceExtension_of_mem (f : HalfEndEntranceValue)
    {x : E3} (hx : x ∈ closedBall (0 : E3) 4) :
    halfEndEntranceExtension f x = f ⟨x, hx⟩ := by
  classical
  simp [halfEndEntranceExtension, halfEndEntranceEval, hx]

@[simp] theorem halfEndEntranceExtension_add (f g : HalfEndEntranceValue) (x : E3) :
    halfEndEntranceExtension (f + g) x =
      halfEndEntranceExtension f x + halfEndEntranceExtension g x :=
  map_add (halfEndEntranceEval x) f g

@[simp] theorem halfEndEntranceExtension_smul (c : ℝ) (f : HalfEndEntranceValue) (x : E3) :
    halfEndEntranceExtension (c • f) x = c * halfEndEntranceExtension f x := by
  exact map_smul (halfEndEntranceEval x) c f

@[simp] theorem halfEndEntranceExtension_sub (f g : HalfEndEntranceValue) (x : E3) :
    halfEndEntranceExtension (f - g) x =
      halfEndEntranceExtension f x - halfEndEntranceExtension g x :=
  map_sub (halfEndEntranceEval x) f g

/-- One physical function is defined from the declared entrance value. -/
def halfEndPhysicalRealization (ε : ℝ) (f : HalfEndEntranceValue) (x : E3) : ℝ :=
  radialScale ε * halfEndEntranceExtension f (ε⁻¹ • x)

theorem halfEndPhysicalRealization_entrance {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndEntranceValue) (z : E3) :
    halfEndCoordinateCorrection ε (halfEndPhysicalRealization ε f) 0 z =
      halfEndEntranceExtension f z := by
  rw [halfEndCoordinateCorrection_zero]
  change (radialScale ε)⁻¹ *
    (radialScale ε * halfEndEntranceExtension f (ε⁻¹ • (ε • z))) = _
  rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul, ← mul_assoc,
    inv_mul_cancel₀ (radialScale_pos ε).ne', one_mul]

theorem halfEndPhysicalRealization_slice {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndEntranceValue) (s : ℝ) (z : E3) :
    halfEndCoordinateCorrection ε (halfEndPhysicalRealization ε f) s z =
      Real.exp (-s / 2) * halfEndEntranceExtension f (Real.exp (-s) • z) := by
  simpa only [zero_add, halfEndPhysicalRealization_entrance hε] using
    halfEndCoordinateCorrection_shift hε (halfEndPhysicalRealization ε f) 0 s z

/-- If the value coordinate is the actual entrance normalization of a
given physical w, reconstruction recovers that same w on the full ball.
This is an equality of the declared functions, not a new local solution. -/
theorem halfEndPhysicalRealization_eq_same_physical {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndEntranceValue) (w : E3 → ℝ)
    (hf : ∀ y : HalfEndEntranceBall,
      f y = halfEndCoordinateCorrection ε w 0 (y : E3)) :
    EqOn (halfEndPhysicalRealization ε f) w (closedBall (0 : E3) (4 * ε)) := by
  intro x hx
  have hxn : ‖x‖ ≤ 4 * ε := by
    simpa only [mem_closedBall, dist_zero_right] using hx
  have hy : ε⁻¹ • x ∈ closedBall (0 : E3) 4 := by
    simp only [mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_pos.mpr hε).le]
    calc
      ε⁻¹ * ‖x‖ ≤ ε⁻¹ * (4 * ε) :=
        mul_le_mul_of_nonneg_left hxn (inv_pos.mpr hε).le
      _ = 4 := by field_simp
  change radialScale ε * halfEndEntranceExtension f (ε⁻¹ • x) = w x
  rw [halfEndEntranceExtension_of_mem f hy, hf,
    halfEndCoordinateCorrection_zero, ← mul_assoc,
    mul_inv_cancel₀ (radialScale_pos ε).ne', one_mul,
    smul_smul, mul_inv_cancel₀ hε.ne', one_smul]

/-- These are exactly e^(2s) times the normalized slices of the single
physical realization, not independently assigned local functions. -/
def halfEndWeightedPhysicalSliceMap :
    HalfEndEntranceValue →ₗ[ℝ] (HalfEndPhysicalSliceIndex → E3 → ℝ) where
  toFun f i z := Real.exp (3 * i.1 / 2) *
    halfEndEntranceExtension f (Real.exp (-i.1) • z)
  map_add' f g := by
    funext i z
    simp only [Pi.add_apply, halfEndEntranceExtension_add]
    ring
  map_smul' c f := by
    funext i z
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
      halfEndEntranceExtension_smul]
    ring

theorem halfEndWeightedPhysicalSliceMap_continuous
    (i : HalfEndPhysicalSliceIndex) (z : E3) :
    Continuous (fun f : HalfEndEntranceValue => halfEndWeightedPhysicalSliceMap f i z) :=
  continuous_const.mul (halfEndEntranceEval (Real.exp (-i.1) • z)).continuous

/-- The short negative collar only reaches radius four, including its
outer boundary. No smooth zero extension beyond that boundary is used. -/
theorem halfEnd_physical_slice_mem_entrance_ball
    (i : HalfEndPhysicalSliceIndex) {z : E3} (hz : ‖z‖ ≤ 2) :
    Real.exp (-i.1) • z ∈ closedBall (0 : E3) 4 := by
  have he : Real.exp (-i.1) ≤ 2 := by
    have h := Real.exp_le_exp.mpr (show -i.1 ≤ Real.log 2 by linarith [i.2])
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  simp only [mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (-i.1) * ‖z‖ ≤ 2 * ‖z‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg z)
    _ ≤ 4 := by linarith

theorem halfEndWeightedPhysicalSliceMap_apply_in_ball
    (f : HalfEndEntranceValue) (i : HalfEndPhysicalSliceIndex) {z : E3}
    (hz : ‖z‖ ≤ 2) :
    halfEndWeightedPhysicalSliceMap f i z =
      Real.exp (3 * i.1 / 2) *
        f ⟨Real.exp (-i.1) • z, halfEnd_physical_slice_mem_entrance_ball i hz⟩ := by
  change Real.exp (3 * i.1 / 2) * halfEndEntranceExtension f (Real.exp (-i.1) • z) = _
  rw [halfEndEntranceExtension_of_mem f (halfEnd_physical_slice_mem_entrance_ball i hz)]

theorem halfEndWeightedPhysicalSliceMap_eq_physical {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndEntranceValue) (i : HalfEndPhysicalSliceIndex) (z : E3) :
    halfEndWeightedPhysicalSliceMap f i z = Real.exp (2 * i.1) *
      halfEndCoordinateCorrection ε (halfEndPhysicalRealization ε f) i.1 z := by
  change Real.exp (3 * i.1 / 2) * halfEndEntranceExtension f (Real.exp (-i.1) • z) = _
  rw [halfEndPhysicalRealization_slice hε]
  have he : Real.exp (3 * i.1 / 2) =
      Real.exp (2 * i.1) * Real.exp (-i.1 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem halfEndBasicAnnulus_isOpen : IsOpen halfEndBasicAnnulus :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- A genuine Banach graph with one physical value coordinate and the
actual uniformly bounded weak H4 jets of its retained weighted slices. -/
abbrev HalfEndPhysicalH4Graph :=
  weakSobolevGraph halfEndBasicAnnulus halfEndBasicAnnulus_isOpen 4
    halfEndWeightedPhysicalSliceMap

instance halfEndPhysicalH4GraphCompleteSpace : CompleteSpace HalfEndPhysicalH4Graph :=
  weakSobolevGraph_completeSpace halfEndBasicAnnulus halfEndBasicAnnulus_isOpen 4
    halfEndWeightedPhysicalSliceMap halfEndWeightedPhysicalSliceMap_continuous

def halfEndPhysicalH4GraphValue : HalfEndPhysicalH4Graph →L[ℝ] HalfEndEntranceValue :=
  weakSobolevGraphValue halfEndBasicAnnulus halfEndBasicAnnulus_isOpen 4
    halfEndWeightedPhysicalSliceMap

theorem halfEndPhysicalH4GraphValue_injective :
    Function.Injective halfEndPhysicalH4GraphValue :=
  weakSobolevGraph_fst_injective halfEndBasicAnnulus halfEndBasicAnnulus_isOpen 4
    halfEndWeightedPhysicalSliceMap

/-- The entire actual weighted weak H4 norm is bounded by the graph norm.
The unweighted slice is the normalization of this same physical function. -/
theorem halfEndPhysicalH4Graph_actual_weighted_bound {ε : ℝ} (hε : 0 < ε)
    (f : HalfEndPhysicalH4Graph) (s : ℝ) (hs : -(Real.log 2) ≤ s) :
    let w := halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue f)
    MemWkp 4 2 (halfEndCoordinateCorrection ε w s) halfEndBasicAnnulus ∧
      ENNReal.ofReal (Real.exp (2 * s)) * iteratedWeakSobolevNorm 4 2
        (halfEndCoordinateCorrection ε w s) halfEndBasicAnnulus ≤ ENNReal.ofReal ‖f‖ := by
  let i : HalfEndPhysicalSliceIndex := ⟨s, hs⟩
  let w := halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue f)
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have heq : halfEndWeightedPhysicalSliceMap f.1.1 i = fun z =>
      Real.exp (2 * s) * halfEndCoordinateCorrection ε w s z := by
    funext z
    exact halfEndWeightedPhysicalSliceMap_eq_physical hε f.1.1 i z
  have hweighted := (f.2 i).1
  have hfinite := (wkpNorm_lt_top_of_memWkp hweighted).ne
  have hbound : iteratedWeakSobolevNorm 4 2
      (halfEndWeightedPhysicalSliceMap f.1.1 i) halfEndBasicAnnulus ≤ ENNReal.ofReal ‖f‖ :=
    (ENNReal.le_ofReal_iff_toReal_le hfinite (norm_nonneg _)).mpr
      (weakSobolevGraph_local_norm_le halfEndBasicAnnulus halfEndBasicAnnulus_isOpen 4
        halfEndWeightedPhysicalSliceMap f i)
  rw [heq] at hweighted
  have hu := MemWkp.const_smul hp halfEndBasicAnnulus_isOpen hweighted
    (Real.exp (2 * s))⁻¹
  have hundo : (fun z => (Real.exp (2 * s))⁻¹ *
      (Real.exp (2 * s) * halfEndCoordinateCorrection ε w s z)) =
        halfEndCoordinateCorrection ε w s := by
    funext z
    rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
  rw [hundo] at hu
  refine ⟨hu, ?_⟩
  rw [heq, wkpNorm_const_smul hp halfEndBasicAnnulus_isOpen hu,
    Real.enorm_eq_ofReal (Real.exp_pos _).le] at hbound
  exact hbound

/-- Convergence in the graph gives pointwise convergence of the same
physical realizations, including all overlap evaluations. -/
theorem halfEndPhysicalH4Graph_same_physical_pointwise_limit
    {f : ℕ → HalfEndPhysicalH4Graph} {F : HalfEndPhysicalH4Graph}
    (hF : Tendsto f atTop (𝓝 F)) (ε : ℝ) (x : E3) :
    Tendsto (fun n => halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue (f n)) x)
      atTop (𝓝 (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue F) x)) := by
  have h : Continuous (fun z : HalfEndPhysicalH4Graph =>
      halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue z) x) :=
    continuous_const.mul ((halfEndEntranceEval (ε⁻¹ • x)).continuous.comp
      halfEndPhysicalH4GraphValue.continuous)
  exact h.continuousAt.tendsto.comp hF

/-- Graph convergence controls the supremum of the actual weak H4 errors
over the entire half-end and its short entrance collar. The one common
graph difference gives one common bound for every logarithmic slice. -/
theorem halfEndPhysicalH4Graph_uniform_weak_h4_convergence
    {ε : ℝ} (hε : 0 < ε)
    {f : ℕ → HalfEndPhysicalH4Graph} {F : HalfEndPhysicalH4Graph}
    (hF : Tendsto f atTop (𝓝 F)) :
    Tendsto (fun n => ⨆ s : ℝ, ⨆ (_hs : -(Real.log 2) ≤ s),
      ENNReal.ofReal (Real.exp (2 * s)) * iteratedWeakSobolevNorm 4 2
        (fun z => halfEndCoordinateCorrection ε
          (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue (f n))) s z -
          halfEndCoordinateCorrection ε
            (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue F)) s z)
        halfEndBasicAnnulus) atTop (𝓝 0) := by
  have hsub (n : ℕ) (s : ℝ) :
      halfEndCoordinateCorrection ε
        (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue (f n - F))) s =
      fun z => halfEndCoordinateCorrection ε
        (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue (f n))) s z -
          halfEndCoordinateCorrection ε
            (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue F)) s z := by
    funext z
    simp only [halfEndCoordinateCorrection, halfEndPhysicalRealization,
      map_sub, halfEndEntranceExtension_sub]
    ring
  have hb (n : ℕ) : (⨆ s : ℝ, ⨆ (_hs : -(Real.log 2) ≤ s),
      ENNReal.ofReal (Real.exp (2 * s)) * iteratedWeakSobolevNorm 4 2
        (fun z => halfEndCoordinateCorrection ε
          (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue (f n))) s z -
          halfEndCoordinateCorrection ε
            (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue F)) s z)
        halfEndBasicAnnulus) ≤ ENNReal.ofReal ‖f n - F‖ := by
    refine iSup_le fun s => iSup_le fun hs => ?_
    have h := (halfEndPhysicalH4Graph_actual_weighted_bound hε (f n - F) s hs).2
    change ENNReal.ofReal (Real.exp (2 * s)) * iteratedWeakSobolevNorm 4 2
      (halfEndCoordinateCorrection ε
        (halfEndPhysicalRealization ε (halfEndPhysicalH4GraphValue (f n - F))) s)
      halfEndBasicAnnulus ≤ ENNReal.ofReal ‖f n - F‖ at h
    rw [hsub n s] at h
    exact h
  have hn : Tendsto (fun n => ‖f n - F‖) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => F) atTop (𝓝 F) := tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hF.sub hconst).norm
  have hne : Tendsto (fun n => ENNReal.ofReal ‖f n - F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hn
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hne δ hδ
  exact ⟨N, fun n hn => (hb n).trans (hN n hn)⟩

#print axioms halfEndWeightedPhysicalSliceMap_eq_physical
#print axioms halfEndPhysicalRealization_eq_same_physical
#print axioms halfEnd_physical_slice_mem_entrance_ball
#print axioms halfEndPhysicalH4GraphCompleteSpace
#print axioms halfEndPhysicalH4GraphValue_injective
#print axioms halfEndPhysicalH4Graph_actual_weighted_bound
#print axioms halfEndPhysicalH4Graph_same_physical_pointwise_limit
#print axioms halfEndPhysicalH4Graph_uniform_weak_h4_convergence

end Yamabe3.Analysis.UniformElliptic
