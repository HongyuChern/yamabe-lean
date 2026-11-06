import Yamabe3.Analysis.SpectralBoundaryPoissonL2

/-! Bounded L2 size of the genuine free Poisson extension and its actual
potential source. Constants precede the boundary vector. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
variable {ι : Type*} (k : ι → ℝ) {k₀ : ℝ} (hk₀ : 2<k₀) (hk : ∀ i,k₀≤k i)

 theorem exists_spectralFullBoundaryPoisson_L2_bound :
    ∃ C : ℝ,0 ≤ C ∧ ∀ b : SpectralSpace ι,
      ‖(spectralFullBoundaryPoisson_memLp k hk₀ hk b).toLp
        (spectralFullBoundaryPoissonCLM k hk₀ hk b)‖ ≤ C*‖b‖ := by
  let a := k₀-2
  let D : ℝ → ℝ := fun t => (2*a)*spectralMajorant a 0 t
  have ha : 0<a := sub_pos.mpr hk₀
  have hD : MemLp D 2 := (spectralMajorant_memLp_two ha (by simpa using ha)).const_mul (2*a)
  have hDn (t : ℝ) : 0 ≤ D t := by dsimp [D,spectralMajorant];positivity
  have hDe (t : ℝ) : D t=Real.exp (-(k₀-2)*|t|) := by
    dsimp [D,spectralMajorant]
    simp only [neg_zero,zero_mul,zero_sub]
    rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) ha.ne')]
    simp only [a,neg_mul]
  refine ⟨(eLpNorm D 2).toReal,ENNReal.toReal_nonneg,?_⟩
  intro b
  have hb : eLpNorm (spectralFullBoundaryPoissonCLM k hk₀ hk b) 2 ≤ eLpNorm (‖b‖ • D) 2 := by
    apply eLpNorm_mono_ae
    exact Eventually.of_forall fun t => by
      change ‖spectralFullBoundaryPoissonCLM k hk₀ hk b t‖ ≤ ‖‖b‖*D t‖
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hDn t)),hDe,mul_comm]
      exact spectralFullBoundaryPoisson_decay k hk₀ hk b t
  rw [eLpNorm_const_smul] at hb
  have ht : ‖‖b‖‖ₑ*eLpNorm D 2≠⊤ := ENNReal.mul_ne_top (by simp) hD.2.ne
  have he := ENNReal.toReal_mono ht hb
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul,enorm_norm,toReal_enorm,mul_comm] using he

 theorem spectralBoundaryPotentialSource_eq_mul (V : ℝ →ᵇ ℝ) (b : SpectralSpace ι) :
    (spectralFullBoundaryPoisson_potential_memLp k hk₀ hk V b).toLp
      ((V • spectralFullBoundaryPoissonCLM k hk₀ hk b : ℝ →ᵇ SpectralSpace ι) : ℝ → SpectralSpace ι)=
      spectralL2PotentialMulCLM V ((spectralFullBoundaryPoisson_memLp k hk₀ hk b).toLp
        (spectralFullBoundaryPoissonCLM k hk₀ hk b)) := by
  apply Lp.ext
  filter_upwards [(spectralFullBoundaryPoisson_potential_memLp k hk₀ hk V b).coeFn_toLp,
    (spectralFullBoundaryPoisson_memLp k hk₀ hk b).coeFn_toLp,
    spectralL2PotentialMul_coe_ae V ((spectralFullBoundaryPoisson_memLp k hk₀ hk b).toLp
      (spectralFullBoundaryPoissonCLM k hk₀ hk b))] with t hF hQ hM
  change _=spectralL2PotentialMul V _ t
  rw [hF,hM]
  change V t • spectralFullBoundaryPoissonCLM k hk₀ hk b t=V t • _
  rw [hQ]

 theorem exists_spectralBoundaryPotentialSource_L2_bound (V : ℝ →ᵇ ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ b : SpectralSpace ι,
      ‖(spectralFullBoundaryPoisson_potential_memLp k hk₀ hk V b).toLp
        ((V • spectralFullBoundaryPoissonCLM k hk₀ hk b : ℝ →ᵇ SpectralSpace ι) : ℝ → SpectralSpace ι)‖ ≤ C*‖b‖ := by
  obtain ⟨C,hC,h⟩ := exists_spectralFullBoundaryPoisson_L2_bound k hk₀ hk
  refine ⟨‖V‖*C,mul_nonneg (norm_nonneg _) hC,fun b => ?_⟩
  rw [spectralBoundaryPotentialSource_eq_mul]
  exact (spectralL2PotentialMul_norm_le V _).trans
    ((mul_le_mul_of_nonneg_left (h b) (norm_nonneg V)).trans_eq (by ring))

#print axioms exists_spectralFullBoundaryPoisson_L2_bound
#print axioms spectralBoundaryPotentialSource_eq_mul
#print axioms exists_spectralBoundaryPotentialSource_L2_bound
end Yamabe3.Analysis.Delaunay
