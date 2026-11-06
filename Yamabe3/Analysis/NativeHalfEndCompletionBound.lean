import Yamabe3.Analysis.NativeHalfEndCompletionChoice

/-! The chosen completion has a homogeneous bound by the original source
graph norm. The constant is fixed before the source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction InnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open PoincareMT.LeviCivitaData.Dirichlet

theorem exists_nativeHalfEnd_completion_bound
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
    (hV0 : ∀ t, 0 ≤ V t) (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : HalfEndHighH2Source,
      ENNReal.ofReal ‖nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f‖ ≤
        C * ENNReal.ofReal ‖f.1‖ := by
  let A : ℝ := ((2 / (((5 / 2 : ℝ)^2 - 4) * (1-κ)^2))^2 / 6 +
        (nativeHalfHighDirichletEnergyBound κ V ^ 2 + nativeHalfHighDirichletDerivativeBound κ V ^ 2) / 2)
  let C := Real.sqrt |A| * ‖nativeSphereL2Inclusion‖
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg nativeSphereL2Inclusion)
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
  intro f
  have h := nativeHalfEndH2SourceCompletion_norm_sq hκ0 hκ1 V hV hV0 hVs f
  have hT : ‖halfEndH2SourceToAngularCLM f.1‖ ≤ ‖nativeSphereL2Inclusion‖ * ‖f.1‖ :=
    halfEndH2SourceToAngularCLM_norm_le f.1
  have hsq : ‖nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f‖^2 ≤ (C*‖f.1‖)^2 := by
    calc
      _ ≤ A * ‖halfEndH2SourceToAngularCLM f.1‖^2 := h
      _ ≤ |A| * (‖nativeSphereL2Inclusion‖ * ‖f.1‖)^2 :=
        mul_le_mul (le_abs_self _) (sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hT)
          (sq_nonneg _) (abs_nonneg _)
      _ = _ := by dsimp only [C]; simp only [mul_pow, Real.sq_sqrt (abs_nonneg A)]; ring
  have hn := le_of_sq_le_sq hsq (mul_nonneg hC (norm_nonneg f.1))
  simpa only [ENNReal.ofReal_mul hC] using ENNReal.ofReal_le_ofReal hn

#print axioms exists_nativeHalfEnd_completion_bound
end Yamabe3.Analysis.UniformElliptic
