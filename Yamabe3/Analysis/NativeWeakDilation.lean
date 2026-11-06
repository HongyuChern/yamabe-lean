import Yamabe3.Analysis.UniformElliptic.HalfEndEntranceCollar
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Iterated.WeakDerivatives

/-!
# Actual weak Sobolev derivatives under a nonzero Euclidean dilation

This supplies the weak, all-order transport missing from the smooth jet
scaling estimates.  The weak derivative is proved by changing variables
in the test integral, including the genuine volume determinant.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem map_restrict_volume_dilation {r : ℝ} (hr : r ≠ 0) (O : Set E) :
    Measure.map (fun x : E => r • x) (volume.restrict ((fun x : E => r • x) ⁻¹' O)) =
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • volume.restrict O := by
  have he : MeasurableEmbedding (fun x : E => r • x) :=
    (Homeomorph.smulOfNeZero r hr : E ≃ₜ E).measurableEmbedding
  rw [← he.restrict_map volume O, Measure.map_addHaar_smul volume hr, Measure.restrict_smul]

theorem memLp_comp_dilation {r : ℝ} (hr : r ≠ 0) {O : Set E}
    {u : E → ℝ} {p : ℝ≥0∞} (hu : MemLp u p (volume.restrict O)) :
    MemLp (fun x : E => u (r • x)) p (volume.restrict ((fun x : E => r • x) ⁻¹' O)) := by
  have he : MeasurableEmbedding (fun x : E => r • x) :=
    (Homeomorph.smulOfNeZero r hr : E ≃ₜ E).measurableEmbedding
  change MemLp (u ∘ (fun x : E => r • x)) p _
  rw [← he.memLp_map_measure_iff, map_restrict_volume_dilation hr]
  exact hu.smul_measure ENNReal.ofReal_ne_top

theorem setIntegral_comp_dilation {r : ℝ} (hr : r ≠ 0) (O : Set E) (u : E → ℝ) :
    (∫ x in (fun x : E => r • x) ⁻¹' O, u (r • x)) =
      |(r ^ Module.finrank ℝ E)⁻¹| * ∫ x in O, u x := by
  have he : MeasurableEmbedding (fun x : E => r • x) :=
    (Homeomorph.smulOfNeZero r hr : E ≃ₜ E).measurableEmbedding
  rw [← he.integral_map u, map_restrict_volume_dilation hr, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

/-- Genuine distributional change of variables, not differentiation of a
chosen measurable representative. -/
theorem hasWeakPartialDeriv_comp_dilation {r : ℝ} (hr : r ≠ 0)
    {O : Set E} {u g : E → ℝ} {i : Fin d}
    (hw : HasWeakPartialDeriv i g u O) :
    HasWeakPartialDeriv i (fun x => r * g (r • x)) (fun x => u (r • x))
      ((fun x : E => r • x) ⁻¹' O) := by
  intro φ hφ hc hs
  let ψ : E → ℝ := fun y => φ (r⁻¹ • y)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.const_smul r⁻¹)
  have hψc : HasCompactSupport ψ :=
    hc.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))
  have hψs : tsupport ψ ⊆ O := by
    intro y hy
    have hpre : r⁻¹ • y ∈ tsupport φ :=
      (tsupport_comp_eq_preimage φ
        (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))).le hy
    have h := hs hpre
    simpa only [mem_preimage, smul_smul, mul_inv_cancel₀ hr, one_smul] using h
  have ht := hw ψ hψ hψc hψs
  have hval (x : E) : ψ (r • x) = φ x := by
    simp only [ψ, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have hder (x : E) :
      r * fderiv ℝ ψ (r • x) (EuclideanSpace.single i 1) =
        fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    dsimp only [ψ]
    rw [fderiv_comp_smul]
    simp only [smul_apply, smul_eq_mul, smul_smul, inv_mul_cancel₀ hr, one_smul]
    rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  calc
    _ = ∫ x in (fun x : E => r • x) ⁻¹' O,
        r * (u (r • x) * fderiv ℝ ψ (r • x) (EuclideanSpace.single i 1)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [mul_left_comm, hder]
    _ = r * (|(r ^ Module.finrank ℝ E)⁻¹| *
        ∫ y in O, u y * fderiv ℝ ψ y (EuclideanSpace.single i 1)) := by
      rw [integral_const_mul, setIntegral_comp_dilation hr O
        (fun y => u y * fderiv ℝ ψ y (EuclideanSpace.single i 1))]
    _ = -(r * (|(r ^ Module.finrank ℝ E)⁻¹| * ∫ y in O, g y * ψ y)) := by
      rw [ht]; ring
    _ = -(∫ x in (fun x : E => r • x) ⁻¹' O, r * (g (r • x) * ψ (r • x))) := by
      rw [integral_const_mul, setIntegral_comp_dilation hr O (fun y => g y * ψ y)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; rw [hval]; ring

/-- The same original function, pulled back by the literal dilation,
has every claimed weak derivative. No smoothness or density input is used. -/
theorem memWkp_comp_dilation {r : ℝ} (hr : r ≠ 0) {O : Set E}
    (hO : IsOpen O) {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ) {u : E → ℝ}
    (hu : MemWkp k p u O) :
    MemWkp k p (fun x : E => u (r • x)) ((fun x : E => r • x) ⁻¹' O) := by
  have hW : IsOpen ((fun x : E => r • x) ⁻¹' O) :=
    hO.preimage (continuous_id.const_smul r)
  induction k generalizing u with
  | zero => exact memLp_comp_dilation hr hu
  | succ k ih =>
    apply memWkp_succ_of_weakDerivatives hW hp (memLp_comp_dilation hr hu.memLp)
      (g := fun i x => r * chosenWeakPartial' p i u O (r • x))
    · intro i
      exact MemWkp.const_smul hp hW (ih (hu.chosenWeakPartial_mem i)) r
    · intro i
      exact hasWeakPartialDeriv_comp_dilation hr
        (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)

#print axioms hasWeakPartialDeriv_comp_dilation
#print axioms memWkp_comp_dilation

end Yamabe3.Analysis.UniformElliptic
