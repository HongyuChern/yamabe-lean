import Yamabe3.Analysis.NativeBubbleDelaunayCoupling
import Yamabe3.Analysis.Cylinder.NativeCylinderPullback

/-!
The same model high Poisson corrections with their actual conformal radial
amplitude. Time is t=-log(r/epsilon). The two one-sided time derivatives
therefore retain the 1/2 value term. At the entrance the sum of outward
8-normal fluxes is (8/epsilon) times exterior-minus-interior time derivative.
This module is a Hilbert-valued model trace/normal result; it makes no
claim that an arbitrary native metric has Euclidean conormal data.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

/-- The literal radial amplitude at physical radius epsilon exp(-t). -/
theorem model_radial_amplitude {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    radialScale (ε * Real.exp (-t)) = radialScale ε * Real.exp (t/2) := by
  unfold radialScale
  rw [Real.log_mul hε.ne' (Real.exp_pos _).ne', Real.log_exp, ← Real.exp_add]
  congr 1
  ring

def modelExteriorPhysicalCurve (P : NativeHighPotential) (ε : ℝ) (b : AngularH1) (t : ℝ) : AngularL2 :=
  (radialScale ε * Real.exp (t/2)) • P.curve b (-t)

def modelInteriorPhysicalCurve (P : NativeHighPotential) (ε : ℝ) (b : AngularH1) (t : ℝ) : AngularL2 :=
  (radialScale ε * Real.exp (t/2)) • P.curve b t

private theorem amplitude_derivative (ε : ℝ) :
    HasDerivAt (fun t : ℝ => radialScale ε * Real.exp (t/2)) (radialScale ε / 2) 0 := by
  apply ((((hasDerivAt_id (0:ℝ)).div_const 2).exp).const_mul (radialScale ε)).congr_deriv
  norm_num
  ring

theorem modelExteriorPhysicalCurve_derivative (P : NativeHighPotential) (ε : ℝ)
    (b : AngularH1) (hb : nativeHighEnergyProjectionCLM b = b) :
    HasDerivWithinAt (modelExteriorPhysicalCurve P ε b)
      (radialScale ε • ((1/2:ℝ) • angularEmbedding b + P.dtn b)) (Iic 0) 0 := by
  have h := (amplitude_derivative ε).hasDerivWithinAt.smul (P.reflected_curve_left_derivative b)
  change HasDerivWithinAt (modelExteriorPhysicalCurve P ε b) _ (Iic 0) 0 at h
  apply h.congr_deriv
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one, P.curve_zero b hb]
  module

theorem modelInteriorPhysicalCurve_derivative (P : NativeHighPotential) (ε : ℝ)
    (b : AngularH1) (hb : nativeHighEnergyProjectionCLM b = b) :
    HasDerivWithinAt (modelInteriorPhysicalCurve P ε b)
      (radialScale ε • ((1/2:ℝ) • angularEmbedding b - P.dtn b)) (Ici 0) 0 := by
  have h := (amplitude_derivative ε).hasDerivWithinAt.smul (P.curve_right_derivative b)
  change HasDerivWithinAt (modelInteriorPhysicalCurve P ε b) _ (Ici 0) 0 at h
  apply h.congr_deriv
  simp only [zero_div, Real.exp_zero, mul_one, P.curve_zero b hb]
  module

/-- One boundary correction produces both true physical-amplitude curves,
their one-sided derivatives, the value jump and the oriented normal sum.
The coefficient 8 and the radial one-half term are not suppressed. -/
theorem exists_actual_high_model_physical_cauchy_matching
    (B W : NativeHighPotential) {ε : ℝ} (hε : 0 < ε)
    (d : AngularH1) (hd : nativeHighEnergyProjectionCLM d = d)
    (ℓ : AngularL2) (hℓ : nativeHighProjection ℓ = ℓ) :
    ∃ (σ : AngularH1) (dout din : AngularL2),
      nativeHighEnergyProjectionCLM σ = σ ∧
      modelExteriorPhysicalCurve B ε (σ+d) 0 - modelInteriorPhysicalCurve W ε σ 0 =
        radialScale ε • angularEmbedding d ∧
      HasDerivWithinAt (modelExteriorPhysicalCurve B ε (σ+d)) dout (Iic 0) 0 ∧
      HasDerivWithinAt (modelInteriorPhysicalCurve W ε σ) din (Ici 0) 0 ∧
      (8/ε : ℝ) • (dout-din) = ℓ := by
  let n : AngularL2 := (ε / (8 * radialScale ε)) • ℓ - (1/2:ℝ) • angularEmbedding d
  have hdh : nativeHighProjection (angularEmbedding d) = angularEmbedding d := by
    rw [← nativeHighEnergyProjectionCLM_embedding, hd]
  have hn : nativeHighProjection n = n := by rw [map_sub, map_smul, hℓ, map_smul, hdh]
  obtain ⟨σ, hs, hsd, _, he⟩ := exists_nativeHighCoupled_cauchy_matching B W d hd n hn
  let dout := radialScale ε • ((1/2:ℝ) • angularEmbedding (σ+d) + B.dtn (σ+d))
  let din := radialScale ε • ((1/2:ℝ) • angularEmbedding σ - W.dtn σ)
  refine ⟨σ, dout, din, hs, ?_, modelExteriorPhysicalCurve_derivative B ε _ hsd,
    modelInteriorPhysicalCurve_derivative W ε _ hs, ?_⟩
  · simp only [modelExteriorPhysicalCurve, modelInteriorPhysicalCurve, neg_zero, zero_div,
      Real.exp_zero, mul_one, B.curve_zero _ hsd, W.curve_zero _ hs, map_add]
    module
  · have he' : dout-din = radialScale ε • ((1/2:ℝ) • angularEmbedding d + n) := by
      dsimp only [dout, din]
      rw [map_add, ← he]
      module
    rw [he']
    dsimp only [n]
    have hcancel : (1/2:ℝ) • angularEmbedding d +
        ((ε / (8 * radialScale ε)) • ℓ - (1/2:ℝ) • angularEmbedding d) =
        (ε / (8 * radialScale ε)) • ℓ := by abel
    rw [hcancel, smul_smul, smul_smul]
    have hc : (8/ε : ℝ) * radialScale ε * (ε/(8*radialScale ε)) = 1 := by
      field_simp [hε.ne', (radialScale_pos ε).ne']
    rw [hc, one_smul]

#print axioms model_radial_amplitude
#print axioms modelExteriorPhysicalCurve_derivative
#print axioms modelInteriorPhysicalCurve_derivative
#print axioms exists_actual_high_model_physical_cauchy_matching
end Yamabe3.Analysis.Delaunay
