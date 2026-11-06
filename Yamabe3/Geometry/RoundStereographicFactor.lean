import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # The exact positive factor of the pinned stereographic coordinates -/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Yamabe3.Geometry

def roundStereographicFactor {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  2 / Real.sqrt (‖x‖ ^ 2 + 4)

theorem roundStereographicFactor_pos {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    0 < roundStereographicFactor x := by
  apply div_pos (by norm_num)
  exact Real.sqrt_pos.mpr (by positivity)

theorem roundStereographicFactor_pow_four {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    roundStereographicFactor x ^ 4 = 16 / (‖x‖ ^ 2 + 4) ^ 2 := by
  have hs : Real.sqrt (‖x‖ ^ 2 + 4) ^ 4 = (‖x‖ ^ 2 + 4) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [roundStereographicFactor, div_pow, hs]
  norm_num

theorem roundStereographicFactor_contDiff {n : ℕ} :
    ContDiff ℝ ∞ (@roundStereographicFactor n) := by
  have hd : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 + 4) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  have hs : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.sqrt (‖x‖ ^ 2 + 4)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (Real.contDiffAt_sqrt (by positivity)).comp x hd.contDiffAt
  exact contDiff_const.div hs (fun x => (Real.sqrt_pos.mpr (by positivity)).ne')

theorem roundStereographicFactor_contMDiff {n : ℕ} :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (@roundStereographicFactor n) :=
  contMDiff_iff_contDiff.mpr roundStereographicFactor_contDiff


#print axioms roundStereographicFactor_contMDiff

end Yamabe3.Geometry
