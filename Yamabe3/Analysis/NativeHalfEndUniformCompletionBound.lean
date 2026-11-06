import Yamabe3.Analysis.NativeHalfEndCompletionBound

/-! A completion norm bound chosen before every potential with a fixed
actual bounded-function norm bound. The explicit energy constants of the
same constructed inverse are controlled on a compact numerical interval. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum

theorem exists_nativeHalfEnd_uniform_completion_bound
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ V : ℝ →ᵇ ℝ, ‖V‖ ≤ M →
      ∀ (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5/2) (-2) s*|V (t-s)|) ≤ κ)
        (hV0 : ∀ t, 0 ≤ V t) (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t))
        (f : HalfEndHighH2Source),
        ENNReal.ofReal ‖nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f‖ ≤
          C*ENNReal.ofReal ‖f.1‖ := by
  let e (t : ℝ) := (20/9:ℝ)*(1+(4/9:ℝ)*t/(1-κ))
  let d (t : ℝ) := (10/9:ℝ)*(1+(4/9:ℝ)*t/(1-κ))+(1+(10/9:ℝ)*t/(1-κ))*e t
  let a (t : ℝ) := (2/(((5/2:ℝ)^2-4)*(1-κ)^2))^2/6+
    ((e t+(1+e t*t)*e t)^2+d t^2)/2
  have ha : Continuous a := by dsimp only [a,d,e]; fun_prop
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := M)).exists_bound_of_continuousOn ha.continuousOn
  let C := Real.sqrt (max 0 B)*‖nativeSphereL2Inclusion‖
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg nativeSphereL2Inclusion)
  refine ⟨ENNReal.ofReal C,ENNReal.ofReal_ne_top,?_⟩
  intro V hVM hV hV0 hVs f
  have hAB : a ‖V‖ ≤ max 0 B :=
    (by simpa only [Real.norm_eq_abs] using le_abs_self (a ‖V‖) : a ‖V‖ ≤ ‖a ‖V‖‖).trans ((hB ‖V‖ ⟨norm_nonneg V,hVM⟩).trans (le_max_right _ _))
  have hnorm := nativeHalfEndH2SourceCompletion_norm_sq hκ0 hκ1 V hV hV0 hVs f
  change ‖nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f‖^2 ≤
    a ‖V‖*‖halfEndH2SourceToAngularCLM f.1‖^2 at hnorm
  have hT := halfEndH2SourceToAngularCLM_norm_le f.1
  have hsq : ‖nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f‖^2 ≤ (C*‖f.1‖)^2 := by
    calc
      _ ≤ a ‖V‖*‖halfEndH2SourceToAngularCLM f.1‖^2 := hnorm
      _ ≤ max 0 B*(‖nativeSphereL2Inclusion‖*‖f.1‖)^2 :=
        mul_le_mul hAB (sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hT)
          (sq_nonneg _) (le_max_left _ _)
      _ = _ := by dsimp only [C]; simp only [mul_pow,Real.sq_sqrt (le_max_left 0 B)]; ring
  have hh := le_of_sq_le_sq hsq (mul_nonneg hC (norm_nonneg f.1))
  simpa only [ENNReal.ofReal_mul hC] using ENNReal.ofReal_le_ofReal hh

#print axioms exists_nativeHalfEnd_uniform_completion_bound
end Yamabe3.Analysis.UniformElliptic
