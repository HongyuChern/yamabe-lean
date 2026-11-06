import Yamabe3.Analysis.UniformWeakDilationNorm
import Yamabe3.Analysis.NativeWeightedTailH4

/-! Uniform dilation of a genuine physical H4 collar through the finite
entrance range. The bound includes every weak derivative and the L2 term. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

def weightedPhysicalDilation (s : ℝ) (u : E → ℝ) (x : E) : ℝ :=
  Real.exp (3*s/2)*u (Real.exp (-s) • x)

theorem finite_weighted_dilation_image {s : ℝ} (hs : -Real.log 2 ≤ s) (hs4 : s ≤ 4) :
    halfEndBasicAnnulus ⊆ (fun x : E => Real.exp (-s) • x) ⁻¹' cylinderAnnulus (-3) 6 := by
  have hl : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  intro x hx
  have hxlo : Real.exp (-Real.log 2) < ‖x‖ := by
    simpa only [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ) < 2),one_div] using hx.1
  have hxhi : ‖x‖ < Real.exp (Real.log 2) := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 2)] using hx.2
  change Real.exp (-6) < ‖Real.exp (-s) • x‖ ∧ ‖Real.exp (-s) • x‖ < Real.exp (-(-3))
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  constructor
  · calc
      _ < Real.exp (-s-Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = Real.exp (-s)*Real.exp (-Real.log 2) := by rw [sub_eq_add_neg,Real.exp_add]
      _ < _ := mul_lt_mul_of_pos_left hxlo (Real.exp_pos _)
  · calc
      _ < Real.exp (-s)*Real.exp (Real.log 2) := mul_lt_mul_of_pos_left hxhi (Real.exp_pos _)
      _ = Real.exp (-s+Real.log 2) := (Real.exp_add _ _).symm
      _ < _ := Real.exp_lt_exp.mpr (by linarith)

theorem exists_finite_weighted_dilation_H4_bound :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u : E → ℝ), MemWkp 4 2 u (cylinderAnnulus (-3) 6) →
      ∀ s : ℝ, -Real.log 2 ≤ s → s ≤ 4 →
        MemWkp 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ∧
        iteratedWeakSobolevNorm 4 2 (weightedPhysicalDilation s u) halfEndBasicAnnulus ≤
          C*iteratedWeakSobolevNorm 4 2 u (cylinderAnnulus (-3) 6) := by
  obtain ⟨D,hD,hb⟩ := exists_uniform_weak_dilation_sobolev_bound (d := 3) 4
    (a := Real.exp (-4)) (b := 2) (Real.exp_pos _)
  refine ⟨ENNReal.ofReal (Real.exp 6)*D,by finiteness,?_⟩
  intro u hu s hs hs4
  have hr0 := Real.exp_pos (-s)
  have hrlo : Real.exp (-4) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have hrhi : Real.exp (-s) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by norm_num)
  have hpre := finite_weighted_dilation_image hs hs4
  have hcomp := memWkp_comp_dilation hr0.ne' (isOpen_cylinderAnnulus (-3) 6) (by norm_num) 4 hu
  have hsmall := hcomp.mono_set (by norm_num) halfEndBasicAnnulus_isOpen hpre
  refine ⟨MemWkp.const_smul (by norm_num) halfEndBasicAnnulus_isOpen hsmall (Real.exp (3*s/2)),?_⟩
  change iteratedWeakSobolevNorm 4 2 (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x)) _ ≤ _
  rw [wkpNorm_const_smul (by norm_num) halfEndBasicAnnulus_isOpen hsmall,Real.enorm_eq_ofReal_abs,
    abs_of_pos (Real.exp_pos _)]
  have hcoef : ENNReal.ofReal (Real.exp (3*s/2)) ≤ ENNReal.ofReal (Real.exp 6) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  have hnorm := (wkpNorm_mono_set (by norm_num) halfEndBasicAnnulus_isOpen hpre hcomp).trans
    (hb _ hrlo hrhi _ (isOpen_cylinderAnnulus (-3) 6) u hu)
  calc
    _ ≤ ENNReal.ofReal (Real.exp 6)*(D*iteratedWeakSobolevNorm 4 2 u (cylinderAnnulus (-3) 6)) :=
      mul_le_mul hcoef hnorm zero_le zero_le
    _ = _ := by ring

#print axioms finite_weighted_dilation_image
#print axioms exists_finite_weighted_dilation_H4_bound
end Yamabe3.Analysis.UniformElliptic
