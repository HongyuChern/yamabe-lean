import Yamabe3.Analysis.AngularValueJetBudget

/-! Actual half-order radial normal trace budget from the same ambient
 two-jet. The induced metric and derivative of df(x)(x) are both used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology ENNReal RealInnerProductSpace lp
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay Poincare.Geometry.Riemannian.SpaceForm
open Yamabe3.Analysis.NativeC1Green
local instance : Fact (Module.finrank ℝ E=2+1):=⟨by simp [E]⟩
private instance (priority:=2000) scalarNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace
private abbrev budgetArea := (roundSphereMetric 2).volumeMeasure

private theorem sphere_restriction_differential {f:E→ℝ} (θ:S)
    (hf:ContDiffAt ℝ ∞ f (θ:E)) (v:TangentSpace (𝓡 2) θ) :
    mvfderiv (𝓡 2) (fun η:S=>f η) θ v=
      fderiv ℝ f (θ:E) (mfderiv (𝓡 2) (𝓡 3) (Subtype.val:S→E) θ v) := by
  have hfm:MDifferentiableAt (𝓡 3) 𝓘(ℝ,ℝ) f (θ:E):=hf.contMDiffAt.mdifferentiableAt (by simp)
  have hι:MDifferentiableAt (𝓡 2) (𝓡 3) (Subtype.val:S→E) θ:=
    (contMDiff_coe_sphere:ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val:S→E)).contMDiffAt.mdifferentiableAt (by simp)
  have hc:=congrArg (fun L=>L v) (mvfderiv_comp θ hfm hι)
  simp only [mvfderiv,mfderiv_eq_fderiv,NormedSpace.fromTangentSpace,ContinuousLinearMap.comp_apply] at hc
  convert! hc using 1

theorem sphere_gradient_restriction_energy_bound {f:E→ℝ} (θ:S)
    (hf:ContDiffAt ℝ ∞ f (θ:E)) {A:ℝ} (hA:0≤A)
    (hd:∀v:E,|fderiv ℝ f (θ:E) v|≤A*‖v‖) :
    (roundSphereMetric 2).inner θ
      (sphereD.gradient (fun η:S=>f η) θ) (sphereD.gradient (fun η:S=>f η) θ)≤A^2 := by
  letI:Bundle.RiemannianBundle (TangentSpace (𝓡 2):S→Type _):=⟨(roundSphereMetric 2).toRiemannianMetric⟩
  let G:=sphereD.gradient (fun η:S=>f η) θ
  let v:E:=mfderiv (𝓡 2) (𝓡 3) (Subtype.val:S→E) θ G
  have hv:‖v‖=‖G‖:=by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq]
    rfl
  have hgrad:(roundSphereMetric 2).inner θ G G=fderiv ℝ f (θ:E) v:=by
    rw [sphereD.inner_gradient]
    exact sphere_restriction_differential θ hf G
  have hg:(roundSphereMetric 2).inner θ G G=‖G‖^2:=by
    change inner ℝ G G=‖G‖^2
    exact real_inner_self_eq_norm_sq G
  have hsq:‖G‖^2≤A*‖G‖:=by
    rw [←hg,hgrad,←hv]
    exact (le_abs_self _).trans (hd v)
  have hn:‖G‖≤A:=by
    by_contra hn
    have hlt:A<‖G‖:=lt_of_not_ge hn
    have hgp:=mul_pos (lt_of_le_of_lt hA hlt) (sub_pos.mpr hlt)
    nlinarith only [hsq,hgp]
  rw [hg]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem angular_half_normal_budget_of_ambient_jets {f:E→ℝ}
    (hf:∀θ:S,ContDiffAt ℝ ∞ f (θ:E)) {A:ℝ} (hA:0≤A)
    (hj:∀j≤2,∀θ:S,‖iteratedFDeriv ℝ j f (θ:E)‖≤A) :
    let H:=fun θ:S=>fderiv ℝ f (θ:E) (θ:E)
    ∃hHs:ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 H,
      NativeAngularSpectralRegular (1/2) (continuousAngularL2 H hHs.continuous) ∧
      (∑'i,nativeAngularWeightedSquare (1/2) (continuousAngularL2 H hHs.continuous) i)≤
        5*(budgetArea univ).toReal*A^2 := by
  let H:E→ℝ:=fun x=>fderiv ℝ f x x
  have hH:∀θ:S,ContDiffAt ℝ ∞ H (θ:E):=by
    intro θ
    exact ((hf θ).fderiv_right (by simp)).clm_apply contDiffAt_id
  have hHs:ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 (fun θ:S=>H θ):=by
    intro θ
    have hc:ContDiffAt ℝ 1 H (θ:E):=(hH θ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
    exact hc.contMDiffAt.comp θ contMDiff_coe_sphere.contMDiffAt
  have hθ:∀θ:S,‖(θ:E)‖=1:=fun θ=>by simpa only [Metric.mem_sphere,dist_zero_right] using θ.property
  have hD (θ:S):‖fderiv ℝ f (θ:E)‖≤A:=by
    simpa only [norm_iteratedFDeriv_one] using hj 1 (by norm_num) θ
  have hDD (θ:S):‖fderiv ℝ (fderiv ℝ f) (θ:E)‖≤A:=by
    rw [←norm_iteratedFDeriv_one (fderiv ℝ f),norm_iteratedFDeriv_fderiv]
    exact hj 2 (le_refl 2) θ
  have hval (θ:S):|H θ|≤A:=by
    have hh:=(fderiv ℝ f (θ:E)).le_opNorm (θ:E)
    rw [hθ θ,mul_one] at hh
    exact (by simpa only [H,Real.norm_eq_abs] using hh.trans (hD θ))
  have hdir (θ:S) (v:E):|fderiv ℝ H (θ:E) v|≤(2*A)*‖v‖:=by
    have hd:(DifferentiableAt ℝ (fderiv ℝ f) (θ:E)):=
      ((hf θ).fderiv_right (by simp):ContDiffAt ℝ ∞ (fderiv ℝ f) (θ:E)).differentiableAt (by simp)
    change |fderiv ℝ (fun x:E=>fderiv ℝ f x (id x)) (θ:E) v|≤_
    rw [fderiv_clm_apply hd differentiableAt_id]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,fderiv_id,ContinuousLinearMap.id_apply,ContinuousLinearMap.flip_apply]
    have h1:|fderiv ℝ f (θ:E) v|≤A*‖v‖:=by
      have hh:|fderiv ℝ f (θ:E) v|≤‖fderiv ℝ f (θ:E)‖*‖v‖:=by
        simpa only [Real.norm_eq_abs] using (fderiv ℝ f (θ:E)).le_opNorm v
      exact hh.trans (mul_le_mul_of_nonneg_right (hD θ) (norm_nonneg _))
    have h2:|fderiv ℝ (fderiv ℝ f) (θ:E) v (θ:E)|≤A*‖v‖:=by
      have hh:=((fderiv ℝ (fderiv ℝ f) (θ:E) v).le_opNorm (θ:E)).trans
        (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ f) (θ:E)).le_opNorm v) (norm_nonneg _))
      rw [hθ θ,mul_one] at hh
      have hh':|fderiv ℝ (fderiv ℝ f) (θ:E) v (θ:E)|≤‖fderiv ℝ (fderiv ℝ f) (θ:E)‖*‖v‖:=by
        simpa only [Real.norm_eq_abs] using hh
      exact hh'.trans (mul_le_mul_of_nonneg_right (hDD θ) (norm_nonneg _))
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have he (θ:S):(roundSphereMetric 2).inner θ (sphereD.gradient (fun θ:S=>H θ) θ)
      (sphereD.gradient (fun θ:S=>H θ) θ)≤(2*A)^2:=
    sphere_gradient_restriction_energy_bound θ (hH θ) (by positivity) (hdir θ)
  have hi1:Integrable (fun θ:S=>H θ*H θ) budgetArea:=
    (hHs.continuous.mul hHs.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2:=integrable_inner_gradient_C1 sphereD hHs hHs (HasCompactSupport.of_compactSpace _)
  have hb:angularC1Pair (fun θ:S=>H θ) (fun θ:S=>H θ)≤5*(budgetArea univ).toReal*A^2:=by
    rw [angularC1Pair,←integral_add hi1 hi2]
    calc
      _ ≤ ∫_θ:S,5*A^2 ∂budgetArea:=integral_mono (hi1.add hi2) (integrable_const _) (fun θ=>by
        have hv:(H θ)^2≤A^2:=by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (H θ)) hA).mpr (hval θ)
        change H θ*H θ+(roundSphereMetric 2).inner θ (sphereD.gradient (fun θ:S=>H θ) θ)
          (sphereD.gradient (fun θ:S=>H θ) θ)≤5*A^2
        nlinarith only [hv,he θ])
      _ = _:=by simp only [integral_const,smul_eq_mul,measureReal_def];ring
  have hs:=angular_C1_half_trace (fun θ:S=>H θ) hHs
  exact ⟨hHs,hs.1,hs.2.trans hb⟩

#print axioms sphere_gradient_restriction_energy_bound
#print axioms angular_half_normal_budget_of_ambient_jets
end Yamabe3.Analysis.SpherePolar
