import Yamabe3.Analysis.SpectralHalfEndPotentialEntrance
import Yamabe3.Analysis.SpectralMajorantL2
import Yamabe3.Analysis.SpectralL2PotentialContinuous

/-! The very same full-line weighted free Poisson extension belongs to
L2. Therefore its potential correction is the already identified L2
inverse, without a new Poisson solution or boundary hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {ι : Type*} (k : ι → ℝ) {k₀ : ℝ} (hk₀ : 2<k₀) (hk : ∀ i,k₀≤k i)

 theorem spectralFullBoundaryPoisson_decay (b : SpectralSpace ι) (t : ℝ) :
    ‖spectralFullBoundaryPoissonCLM k hk₀ hk b t‖≤
      Real.exp (-(k₀-2)*|t|)*‖b‖ := by
  have he : spectralFullBoundaryPoissonCLM k hk₀ hk b t=
      Real.exp (2*t) • spectralPoissonKernel k (by linarith : 0<k₀) hk t b := by
    ext i
    rw [spectralFullBoundaryPoissonCLM_coordinate]
    change _=Real.exp (2*t)*(Real.exp (-k i*|t|)*b i)
    rw [←mul_assoc,←Real.exp_add]
    congr 2
    ring
  rw [he,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (2*t)*(Real.exp (-k₀*|t|)*‖b‖) := mul_le_mul_of_nonneg_left
      (((spectralPoissonKernel k (by linarith) hk t).le_opNorm b).trans
        (mul_le_mul_of_nonneg_right (spectralPoissonKernel_norm_le k (by linarith) hk t) (norm_nonneg b)))
      (Real.exp_pos _).le
    _ ≤ Real.exp (-(k₀-2)*|t|)*‖b‖ := by
      rw [←mul_assoc,←Real.exp_add]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (by linarith [le_abs_self t])

 theorem spectralFullBoundaryPoisson_memLp (b : SpectralSpace ι) :
    MemLp (spectralFullBoundaryPoissonCLM k hk₀ hk b) 2 := by
  let a := k₀-2
  have ha : 0<a := sub_pos.mpr hk₀
  have h := (spectralMajorant_memLp_two ha (by simpa using ha : |(0:ℝ)|<a)).const_mul (2*a*‖b‖)
  apply h.mono (spectralFullBoundaryPoissonCLM k hk₀ hk b).continuous.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  apply (spectralFullBoundaryPoisson_decay k hk₀ hk b t).trans_eq
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
    (show 0≤spectralMajorant a 0 t by unfold spectralMajorant;positivity))]
  unfold spectralMajorant
  simp only [neg_zero,zero_mul,zero_sub]
  dsimp only [a]
  field_simp [(sub_pos.mpr hk₀).ne']
  <;> ring

 theorem spectralFullBoundaryPoisson_potential_memLp (V : ℝ →ᵇ ℝ) (b : SpectralSpace ι) :
    MemLp (V • spectralFullBoundaryPoissonCLM k hk₀ hk b) 2 := by
  apply ((spectralFullBoundaryPoisson_memLp k hk₀ hk b).const_smul ‖V‖).mono
    (V • spectralFullBoundaryPoissonCLM k hk₀ hk b).continuous.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    change ‖V t • spectralFullBoundaryPoissonCLM k hk₀ hk b t‖≤‖‖V‖ • spectralFullBoundaryPoissonCLM k hk₀ hk b t‖
    simpa only [norm_smul,Real.norm_eq_abs,abs_norm] using mul_le_mul_of_nonneg_right
      (V.norm_coe_le_norm t) (norm_nonneg (spectralFullBoundaryPoissonCLM k hk₀ hk b t))

 theorem spectralHalfFullCorrection_eq_L2 {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
    (hminus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ (-2) s*|V (t-s)|)≤κ)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant k₀ 2 s*|V (t-s)|)≤κ)
    (b : SpectralSpace ι) :
    spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hminus b=
      spectralL2PotentialContinuousCLM k (by linarith : 0<k₀) hk
        (by norm_num;exact hk₀ : |(-2:ℝ)|<k₀) V
        ((spectralFullBoundaryPoisson_potential_memLp k hk₀ hk V b).toLp
          ((V • spectralFullBoundaryPoissonCLM k hk₀ hk b : ℝ →ᵇ SpectralSpace ι) : ℝ → SpectralSpace ι)) := by
  rw [spectralHalfFullPotentialCorrectionCLM_apply]
  exact (spectralL2PotentialContinuous_agrees_original k (by linarith) hk
    (by norm_num;exact hk₀ : |(-2:ℝ)|<k₀) hκ0 hκ1 V hminus (by simpa using hplus)
    (V • spectralFullBoundaryPoissonCLM k hk₀ hk b)
    (spectralFullBoundaryPoisson_potential_memLp k hk₀ hk V b)).symm

#print axioms spectralFullBoundaryPoisson_decay
#print axioms spectralFullBoundaryPoisson_memLp
#print axioms spectralFullBoundaryPoisson_potential_memLp
#print axioms spectralHalfFullCorrection_eq_L2
end Yamabe3.Analysis.Delaunay
