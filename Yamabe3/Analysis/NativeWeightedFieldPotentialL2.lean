import Yamabe3.Analysis.NativePhysicalShellAssembly
import Yamabe3.Analysis.NativeScaledJetRepresentation
import Yamabe3.Analysis.NativeCollarPotentialMultiplier

/-! Uniform TRUE weighted collar values make the inverse-square
potential of this SAME field L2 inside the unit ball. No globally
bounded singular potential, nor a general H1 multiplication, is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology ENNReal BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic

theorem native_weighted_field_inverse_square_memLp
    (J:ℕ→nativeCollarJetClosure) (u:E→ℝ)
    (hJ:∀n,(J n).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun x=>Real.exp (3*nativeLogShellCenter n/2)*u (Real.exp (-nativeLogShellCenter n) • x))
    {C:ℝ} (hC:0≤C) (hb:∀n,‖J n‖≤C) :
    MemLp (fun x=>‖x‖⁻¹^2*u x) 2 (volume.restrict (ball (0:E) 1\{0})) := by
  let V:ℝ→ᵇℝ:=BoundedContinuousFunction.const ℝ (1:ℝ)
  let U:ℕ→NativeCollarL2:=fun n=>nativeCollarPotentialMulCLM V (J n).val.1
  have hVnorm:‖V‖=1:=by simp only [V,BoundedContinuousFunction.norm_const_eq,norm_one]
  have hU(n:ℕ):‖U n‖≤(Real.exp 1)*C:=by
    have hn:‖U n‖≤(‖V‖*Real.exp 1)*‖(J n).val.1‖:=by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [nativeCollarPotentialMulCLM_ae V (J n).val.1,
        ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx hxO
      rw [hx,norm_mul]
      exact mul_le_mul_of_nonneg_right (nativeCollarPotential_bound V hxO) (norm_nonneg _)
    have hval:‖(J n).val.1‖≤C:=(norm_fst_le (J n).val).trans (hb n)
    rw [hVnorm,one_mul] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left hval (Real.exp_pos _).le)
  have hm:=nativePhysicalShellAssembly_memLp U (mul_nonneg (Real.exp_pos _).le hC) hU
  apply hm.ae_eq
  rw [←nativePhysicalShell_union,ae_eq_restrict_iUnion_iff]
  intro n
  let s:=nativeLogShellCenter n
  have hrow:(U n:E→ℝ)=ᵐ[volume.restrict nativeSourceShell]
      fun y=>‖y‖⁻¹^2*(Real.exp (3*s/2)*u (Real.exp (-s) • y)):=by
    filter_upwards [ae_mono (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl)
        (nativeCollarPotentialMulCLM_ae V (J n).val.1),
      ae_mono (Measure.restrict_mono nativeSourceShell_subset_collar le_rfl) (hJ n)] with y hy hj
    change (nativeCollarPotentialMulCLM V (J n).val.1:E→ℝ) y=_
    rw [hy,hj]
    simp only [nativeHalfEndPotentialCoefficient,V,BoundedContinuousFunction.const_apply',
      one_div,inv_pow,s]
  have hd:=ae_comp_dilation (Real.exp_ne_zero s) hrow
  change (fun x:E=>(U n:E→ℝ) (Real.exp s • x))=ᵐ[volume.restrict
    ((fun x:E=>Real.exp s • x) ⁻¹' nativeSourceShell)] _ at hd
  rw [←nativePhysicalShell_dilation n] at hd
  filter_upwards [hd,ae_restrict_mem (nativePhysicalShell_measurable n)] with x hx hxO
  rw [nativePhysicalShellAssembly_on U n hxO]
  change Real.exp (s/2)*(U n:E→ℝ) (Real.exp s • x)=_
  rw [hx]
  have hx0:x≠0:=hxO.1
  have he:Real.exp (s/2)*Real.exp (3*s/2)=(Real.exp s)^2:=by
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,smul_smul,
    ←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  field_simp [Real.exp_ne_zero s,norm_ne_zero_iff.mpr hx0]
  rw [show s*3/2=3*s/2 by ring]
  linear_combination (u x)*he

theorem native_weighted_field_potential_memLp
    (J:ℕ→nativeCollarJetClosure) (u:E→ℝ) (hum:Measurable u)
    (hJ:∀n,(J n).val.1=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun x=>Real.exp (3*nativeLogShellCenter n/2)*u (Real.exp (-nativeLogShellCenter n) • x))
    {C:ℝ} (hC:0≤C) (hb:∀n,‖J n‖≤C) (V:ℝ→ᵇℝ) :
    MemLp (fun x=>nativeHalfEndPotentialCoefficient V x*u x) 2
      (volume.restrict (ball (0:E) 1\{0})) := by
  have hm:=native_weighted_field_inverse_square_memLp J u hJ hC hb
  apply hm.of_le_mul (c:=‖V‖) ((nativeCollarPotential_measurable V).mul hum).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  have he:nativeHalfEndPotentialCoefficient V x*u x=V (-Real.log ‖x‖)*(‖x‖⁻¹^2*u x):=by
    simp only [nativeHalfEndPotentialCoefficient,div_eq_mul_inv,inv_pow]
    ring
  change ‖nativeHalfEndPotentialCoefficient V x*u x‖≤_
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_right (V.norm_coe_le_norm _) (norm_nonneg _)

#print axioms native_weighted_field_inverse_square_memLp
#print axioms native_weighted_field_potential_memLp
end Yamabe3.Analysis.SpherePolar
