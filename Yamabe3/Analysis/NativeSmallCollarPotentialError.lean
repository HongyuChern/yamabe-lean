import Yamabe3.Analysis.NativeCollarLocalMultiplier
import Yamabe3.Analysis.UniformElliptic.NativeDelaunayPotentialError
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The actual scalar-curvature/density Delaunay error is a uniformly
small multiplier on the collar, with scale chosen before orbit and phase. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Delaunay

theorem nativeEntranceCollar_annular {x : E} (hx : x ∈ nativePoissonEntranceCollar) :
    (1/2:ℝ)≤‖x‖ ∧ ‖x‖≤2 := by
  have he : Real.exp (1/2:ℝ)<2 := by
    have hprod : Real.exp (1/2:ℝ)*Real.exp (1/2:ℝ)=Real.exp 1 := by
      rw [← Real.exp_add];norm_num
    nlinarith [Real.exp_pos (1/2:ℝ),Real.exp_one_lt_three]
  have hl : (1/2:ℝ)<Real.exp (-(1/2:ℝ)) := by
    have hprod : Real.exp (-(1/2:ℝ))*Real.exp (1/2:ℝ)=1 := by
      rw [← Real.exp_add];norm_num
    nlinarith [Real.exp_pos (-(1/2:ℝ))]
  have hh := (nativePolarTimeWindow_norm (1/2) x).mp hx
  exact ⟨(hl.trans hh.1).le,(hh.2.trans he).le⟩

def nativeCollarPotentialErrorCLM (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) : NativeCollarL2 →L[ℝ] NativeCollarL2 :=
  nativeCollarLocalMulCLM (nativeDelaunayPotentialError g r v phase)
    (fun x hx => (contDiffAt_nativeDelaunayPotentialError g r hv phase hx).continuousAt.continuousWithinAt)

theorem nativeCollarPotentialErrorCLM_ae (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) (F : NativeCollarL2) :
    (nativeCollarPotentialErrorCLM g r v hv phase F : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => nativeDelaunayPotentialError g r v phase x*F x) :=
  nativeCollarLocalMulCLM_ae _ _ F

theorem exists_uniform_small_native_collar_potential_error
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1)
    {τ : ℝ} (hτ : 0<τ) :
    ∃ δ : ℝ,0<δ ∧ ∀ r : ℝ,0≤r → r<δ → ∀ p ∈ Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0≤v t ∧ v t≤1 ∧ |deriv v t|≤1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) →
      ∀ (phase : ℝ) (F : NativeCollarL2),
      ‖nativeCollarPotentialErrorCLM (g p) r v hv phase F‖≤τ*‖F‖ := by
  obtain ⟨δ,hδ,hsmall⟩ := exists_uniform_small_finite_native_delaunay_potential_error Λ g hρ 0 hτ
  refine ⟨δ,hδ,fun r hr hrδ p hp v hv hb ho phase F => ?_⟩
  apply nativeCollarLocalMulCLM_norm_le _ _ hτ.le
  intro x hx
  have h := nativeEntranceCollar_annular hx
  simpa only [norm_iteratedFDeriv_zero] using hsmall r hr hrδ p hp v hv hb ho phase 0 (by omega) x h.1 h.2

#print axioms nativeEntranceCollar_annular
#print axioms nativeCollarPotentialErrorCLM_ae
#print axioms exists_uniform_small_native_collar_potential_error
end Yamabe3.Analysis.SpherePolar
