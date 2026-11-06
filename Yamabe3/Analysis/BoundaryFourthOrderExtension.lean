import Yamabe3.Analysis.BoundaryHigherReflection

/-! Concrete order-four extension. The coefficients 10,-20,15,-4 with
normal samples -1,-2,-3,-4 match all boundary moments through order three.
The weak H4 proof and bound require no boundary jet inputs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.BoundaryTangential Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def reflectionFourRates (j : Fin 4) : ℝ := (j.val : ℝ) + 1
def reflectionFourCoeffs : Fin 4 → ℝ := ![10, -20, 15, -4]

theorem reflectionFourRates_pos (j : Fin 4) : 0 < reflectionFourRates j := by
  dsimp [reflectionFourRates]
  positivity

theorem reflectionFour_moments (q : ℕ) (hq : q < 4) :
    ∑ j : Fin 4, reflectionFourCoeffs j * (-reflectionFourRates j)^q = 1 := by
  interval_cases q <;> norm_num [Fin.sum_univ_succ, reflectionFourCoeffs, reflectionFourRates]

def fourthOrderExtension (u : E → ℝ) : E → ℝ :=
  finiteReflection reflectionFourRates reflectionFourRates_pos reflectionFourCoeffs u

theorem fourthOrderExtension_eq_on (u : E → ℝ) :
    EqOn (fourthOrderExtension u) u (halfSpace d) :=
  finiteReflection_eq_on_halfSpace reflectionFourRates reflectionFourRates_pos reflectionFourCoeffs u

theorem fourthOrderExtension_add (u v : E → ℝ) :
    fourthOrderExtension (u+v) = fourthOrderExtension u + fourthOrderExtension v :=
  finiteReflection_add reflectionFourRates reflectionFourRates_pos reflectionFourCoeffs u v

theorem fourthOrderExtension_smul (a : ℝ) (u : E → ℝ) :
    fourthOrderExtension (a • u) = a • fourthOrderExtension u :=
  finiteReflection_smul reflectionFourRates reflectionFourRates_pos reflectionFourCoeffs a u

/-- The bound precedes the input; all four actual weak orders are outputs.
This local Euclidean half-space result still requires collar patching. -/
theorem exists_fourthOrderExtension_bound :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : E → ℝ,
      MemWkp 4 2 u (halfSpace d) →
      MemWkp 4 2 (fourthOrderExtension u) univ ∧
      iteratedWeakSobolevNorm 4 2 (fourthOrderExtension u) univ ≤
        C * iteratedWeakSobolevNorm 4 2 u (halfSpace d) :=
  exists_finiteReflection_sobolev_bound 4 reflectionFourRates reflectionFourRates_pos
    reflectionFourCoeffs reflectionFour_moments

#print axioms reflectionFour_moments
#print axioms fourthOrderExtension_eq_on
#print axioms fourthOrderExtension_add
#print axioms fourthOrderExtension_smul
#print axioms exists_fourthOrderExtension_bound
end Yamabe3.Analysis.UniformElliptic
