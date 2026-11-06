import Yamabe3.Analysis.NativeWeightedLift
import Yamabe3.Analysis.NativeWeightedEquation
import PoincareLib.Analysis.Sobolev.Euclidean.L2

/-! A source-homogeneous L2 bound for the literal weighted same field on
every fixed physical shell, with the constant preceding orbit and phase. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_native_weighted_shell_L2_bound
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (a b : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (p : DelaunayPhaseData κ) (f : HalfEndHighH2Source) (s : ℝ),
      MemLp (actualWeightedHalfEndField hκ0 hκ1 p f s) 2 (volume.restrict (cylinderShell a b)) ∧
      eLpNorm (actualWeightedHalfEndField hκ0 hκ1 p f s) 2 (volume.restrict (cylinderShell a b)) ≤
        C*ENNReal.ofReal ‖f.1‖ := by
  let J := ∫ t in Icc a b, Real.exp (-6*t)
  have hJ : 0 ≤ J := integral_nonneg (fun _ => (Real.exp_pos _).le)
  let D := 2/(((5/2:ℝ)^2-4)*(1-κ)^2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let S := ‖nativeSphereL2Inclusion‖
  have hS : 0 ≤ S := norm_nonneg nativeSphereL2Inclusion
  refine ⟨ENNReal.ofReal (Real.sqrt J*D*S),ENNReal.ofReal_ne_top,?_⟩
  intro p f s
  let U := nativeHalfHighDirichletPhysical hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
    (halfEndH2SourceToAngularCLM f.1)
  let w := nativeHalfEndH2SourceJoint hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg f
  have hbound (t : ℝ) : ‖U t‖ ≤ Real.exp (-2*t)*(D*S*‖f.1‖) := by
    have hh := nativeHalfHighDirichletPhysical_norm_le hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
      (halfEndH2SourceToAngularCLM f.1) t
    calc
      _ ≤ Real.exp (-2*t)*D*‖halfEndH2SourceToAngularCLM f.1‖ := by simpa only [U,D,mul_assoc] using hh
      _ ≤ Real.exp (-2*t)*D*(S*‖f.1‖) :=
        mul_le_mul_of_nonneg_left (halfEndH2SourceToAngularCLM_norm_le f.1) (mul_nonneg (Real.exp_pos _).le hD)
      _ = _ := by ring
  have hh := weighted_lift_shell_square_bound
    (nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _)
    (nativeHalfHighDirichletJoint_measurable hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _)
    (nativeHalfHighDirichletJoint_ae hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _)
    (D*S*‖f.1‖) hbound s a b
  refine ⟨hh.1,?_⟩
  have hn := Poincare.Analysis.Sobolev.eLpNorm_two_le_sqrt_of_integral_sq_le hh.1 hh.2
  change eLpNorm (actualWeightedHalfEndField hκ0 hκ1 p f s) 2 _ ≤
    ENNReal.ofReal (Real.sqrt (J*(D*S*‖f.1‖)^2)) at hn
  have he : Real.sqrt (J*(D*S*‖f.1‖)^2) = (Real.sqrt J*D*S)*‖f.1‖ := by
    rw [Real.sqrt_mul hJ,Real.sqrt_sq (mul_nonneg (mul_nonneg hD hS) (norm_nonneg f.1))]
    ring
  rw [he,ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hD) hS)] at hn
  exact hn

#print axioms exists_native_weighted_shell_L2_bound
end Yamabe3.Analysis.UniformElliptic
