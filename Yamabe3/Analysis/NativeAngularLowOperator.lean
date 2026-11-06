import Yamabe3.Analysis.NativeAngularInverse
import Yamabe3.Analysis.DelaunayLowFutureInverse

/-!
# The actual bounded low-angular Jacobi coefficient operator

The proved native spectrum supplies only mu=0 or mu=2 below six. The
actual common potential therefore gives an operator norm at most 7/2.
Operator-norm continuity is proved by an exact fixed-diagonal decomposition,
not by pointwise coordinate continuity alone.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

abbrev AngularSpectralSpace := SpectralSpace AngularIndex

def lowAngularCoefficient (v : ℝ → ℝ) (t : ℝ) (i : AngularIndex) : ℝ :=
  if angularEigenvalue i < 6 then 1 / 4 + angularEigenvalue i - (15 / 4) * v t ^ 4 else 0

theorem lowAngularCoefficient_bound {v : ℝ → ℝ}
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (t : ℝ) (i : AngularIndex) :
    |lowAngularCoefficient v t i| ≤ 7 / 2 := by
  unfold lowAngularCoefficient
  split_ifs with hi
  · rcases angularEigenvalue_zero_two_or_ge_six i with h0 | h2 | h6
    · rw [h0]
      exact lowJacobiCoefficient_abs_le hb (by norm_num) (by norm_num) t
    · rw [h2]
      exact lowJacobiCoefficient_abs_le hb (by norm_num) (by norm_num) t
    · exact (not_lt_of_ge h6 hi).elim
  · norm_num

def lowAngularOperator (v : ℝ → ℝ) (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (t : ℝ) :
    AngularSpectralSpace →L[ℝ] AngularSpectralSpace :=
  spectralDiagonal (lowAngularCoefficient v t) (by norm_num) (lowAngularCoefficient_bound hb t)

theorem lowAngularOperator_apply (v : ℝ → ℝ) (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1)
    (t : ℝ) (u : AngularSpectralSpace) (i : AngularIndex) :
    lowAngularOperator v hb t u i = lowAngularCoefficient v t i * u i := rfl

theorem lowAngularOperator_norm_le (v : ℝ → ℝ) (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (t : ℝ) :
    ‖lowAngularOperator v hb t‖ ≤ 7 / 2 := spectralDiagonal_norm_le _ _ _

/-- Actual operator-norm continuity, via two fixed native diagonal maps. -/
theorem continuous_lowAngularOperator {v : ℝ → ℝ} (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) : Continuous (lowAngularOperator v hb) := by
  have hc (i : AngularIndex) :
      |if angularEigenvalue i < 6 then 1 / 4 + angularEigenvalue i else (0 : ℝ)| ≤ 9 / 4 := by
    split_ifs with hi
    · rcases angularEigenvalue_zero_two_or_ge_six i with h0 | h2 | h6
      · rw [h0]; norm_num
      · rw [h2]; norm_num
      · exact (not_lt_of_ge h6 hi).elim
    · norm_num
  let D := spectralDiagonal (fun i => if angularEigenvalue i < 6 then 1 / 4 + angularEigenvalue i else 0)
    (by norm_num : (0 : ℝ) ≤ 9 / 4) hc
  let P := spectralDiagonal (fun i => if angularEigenvalue i < 6 then (1 : ℝ) else 0)
    (by norm_num : (0 : ℝ) ≤ 1) (fun i => by split_ifs <;> norm_num)
  have he : lowAngularOperator v hb = fun t => D - ((15 / 4) * v t ^ 4) • P := by
    funext t
    ext u i
    change lowAngularCoefficient v t i * u i =
      (if angularEigenvalue i < 6 then 1 / 4 + angularEigenvalue i else 0) * u i -
        ((15 / 4) * v t ^ 4) * ((if angularEigenvalue i < 6 then 1 else 0) * u i)
    unfold lowAngularCoefficient
    split_ifs <;> ring
  rw [he]
  exact continuous_const.sub ((continuous_const.mul (hv.pow 4)).smul continuous_const)

/-- The genuine bounded continuous operator coefficient used by the
aggregate Banach future inverse. -/
def lowAngularOperatorBCF (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) : ℝ →ᵇ (AngularSpectralSpace →L[ℝ] AngularSpectralSpace) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (lowAngularOperator v hb)
    (continuous_lowAngularOperator hv hb) (7 / 2) (lowAngularOperator_norm_le v hb)

theorem lowAngularOperatorBCF_norm_le (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) : ‖lowAngularOperatorBCF v hv hb‖ ≤ 7 / 2 :=
  (BoundedContinuousFunction.norm_le (by norm_num)).mpr (lowAngularOperator_norm_le v hb)

end Yamabe3.Analysis.Delaunay
