import Yamabe3.Analysis.NativeActualCoreOperatorIdentity
import Yamabe3.Analysis.NativeCompactChartSource

/-! Exact physical-volume pairing of one actual native smooth core
operator with its normalized unit source. The radius factor is 8a in
dimension3. All tests are of the SAME field; no sphere restriction of
volume-a.e. data is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix NativeChartSphereMetric PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeCore_actual_source_physical_pairing
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hKs:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {a:ℝ} (ha:0<a) (hfit:euclideanDilatedDomain a (ball (0:E) 4)⊆closedBall (0:E) R₀)
    (χ F:E→ℝ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆ball (0:E) 3)
    (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1))
    (hzero:∀x∈closedBall (0:E) 4,
      Poincare.Analysis.Elliptic.InteriorEstimates.principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x+
        a^2*nativePotentialDensity gE (a • x)*F x=0)
    (ψ:EnergyTest g.leviCivitaData univ)
    (hcoord:(ψ:M→ℝ)=coordinateExtension e (fun x:E=>χ (a⁻¹ • x)*F (a⁻¹ • x)))
    (hop:∀x∈ball (0:E) 4,nativeCoreUnitOperator gE a χ F x=
      (a^2*gE.pullbackVolumeDensity id (a • x)/8)*
        (-8*g.leviCivitaData.laplacian ψ (e (a • x))+
          g.leviCivitaData.scalarCurvature (e (a • x))*ψ (e (a • x))))
    (η:EnergyTest g.leviCivitaData univ) (φ:E→ℝ)
    (htest:∀x∈closedBall (0:E) (7/2:ℝ),φ x=η (e (a • x))):
    (∫y,(-8*g.leviCivitaData.laplacian ψ y+g.leviCivitaData.scalarCurvature y*ψ y)*η y ∂g.volumeMeasure)=
      8*a*(∫x:E,nativeCoreUnitOperator gE a χ F x*φ x):=by
  let K:=euclideanDilatedDomain a (closedBall (0:E) (7/2:ℝ))
  let A:M→ℝ:=fun y=>-8*g.leviCivitaData.laplacian ψ y+g.leviCivitaData.scalarCurvature y*ψ y
  let H:=nativeCoreUnitOperator gE a χ F
  have hK:IsCompact K:=
    (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'):E≃ₜE).isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hK4:K⊆euclideanDilatedDomain a (ball (0:E) 4):=preimage_mono (closedBall_subset_ball (by norm_num:(7/2:ℝ)<4))
  have hKsource:K⊆e.source:=(hK4.trans hfit).trans hKs
  have hψs:tsupport (ψ:M→ℝ)⊆e '' K:=by
    rw [hcoord]
    have hcf:HasCompactSupport (fun x:E=>χ (a⁻¹ • x)*F (a⁻¹ • x)):=
      hc.comp_homeomorph (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne')) |>.mul_right
    have hsf:tsupport (fun x:E=>χ (a⁻¹ • x)*F (a⁻¹ • x))⊆K:=by
      apply tsupport_mul_subset_left.trans
      change tsupport (χ ∘ (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'):E≃ₜE))⊆_
      rw [tsupport_comp_eq_preimage]
      exact preimage_mono (hs.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num:(3:ℝ)≤7/2))))
    exact (tsupport_coordinateExtension_subset_image e hcf (hsf.trans hKsource)).trans (image_mono hsf)
  have hAz(y:M)(hy:y∉e '' K):A y=0:=by
    have hn:y∉tsupport (ψ:M→ℝ):=fun h=>hy (hψs h)
    dsimp only [A]
    rw [g.leviCivitaData.laplacian_eq_zero_of_notMem_tsupport hn,image_eq_zero_of_notMem_tsupport hn]
    ring
  have hAm:Measurable A:=((contMDiff_const.mul (g.leviCivitaData.contMDiff_laplacian ψ.smooth)).add
    (g.leviCivitaData.contMDiff_scalarCurvature.mul ψ.smooth)).continuous.measurable
  have heq(x:E)(hx:x∈K):A (e x)*g.pullbackVolumeDensity e x=(8/a^2)*H (a⁻¹ • x):=by
    have hx4:a⁻¹ • x∈ball (0:E) 4:=hK4 hx
    have hop':H (a⁻¹ • x)=(a^2*gE.pullbackVolumeDensity id x/8)*A (e x):=by
      have hh:=hop (a⁻¹ • x) hx4
      simpa only [H,A,smul_smul,mul_inv_cancel₀ ha.ne',one_smul] using hh
    rw [←pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x (hfit hx4))]
    field_simp [ha.ne'] at hop' ⊢
    nlinarith only [hop']
  have hDin:(fun x:E=>(1/2:ℝ) • x) ⁻¹' nativePoissonEntranceCollar⊆closedBall (0:E) (7/2:ℝ):=by
    intro x hx
    have hn:‖(1/2:ℝ) • x‖<Real.exp (1/2:ℝ):=(nativePolarTimeWindow_norm (1/2) _).mp hx |>.2
    rw [norm_smul,Real.norm_of_nonneg (by norm_num:(0:ℝ)≤1/2)] at hn
    have hp:Real.exp (1/2:ℝ)*Real.exp (1/2:ℝ)=Real.exp 1:=by rw [←Real.exp_add];norm_num
    have he:Real.exp (1/2:ℝ)<7/4:=by nlinarith [Real.exp_pos (1/2:ℝ),Real.exp_one_lt_three]
    rw [mem_closedBall_zero_iff]
    linarith
  calc
    _ = ∫y in e '' K,A y*η y ∂g.volumeMeasure:=by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [hAz y hy,zero_mul]
    _ = ∫x in K,A (e x)*η (e x)*g.pullbackVolumeDensity e x:=
      integral_compact_image_eq_pullback_density (g:=g) e he hei hK hKsource (hAm.mul η.smooth.continuous.measurable)
    _ = (8/a^2)*(∫x in K,H (a⁻¹ • x)*φ (a⁻¹ • x)):=by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      have ht:φ (a⁻¹ • x)=η (e x):=by
        simpa only [smul_smul,mul_inv_cancel₀ ha.ne',one_smul] using htest (a⁻¹ • x) hx
      rw [ht,show A (e x)*η (e x)*g.pullbackVolumeDensity e x=(A (e x)*g.pullbackVolumeDensity e x)*η (e x) by ring,heq x hx]
      ring
    _ = (8/a^2)*(a^3*(∫x in closedBall (0:E) (7/2:ℝ),H x*φ x)):=by
      congr 1
      have hd:=setIntegral_comp_dilation (r:=a⁻¹) (inv_ne_zero ha.ne') (closedBall (0:E) (7/2:ℝ)) (fun x:E=>H x*φ x)
      simpa only [K,euclideanDilatedDomain,finrank_euclideanSpace_fin,inv_pow,inv_inv,abs_of_nonneg (pow_nonneg ha.le 3)] using hd
    _ = 8*a*(∫x in closedBall (0:E) (7/2:ℝ),H x*φ x):=by
      field_simp [ha.ne']
      <;>ring
    _ = _:=by
      congr 1
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hn:x∉(fun x:E=>(1/2:ℝ) • x) ⁻¹' nativePoissonEntranceCollar:=fun h=>hx (hDin h)
      change nativeCoreUnitOperator gE a χ F x*φ x=0
      rw [nativeCoreUnitOperator_zero_off_incoming gE a χ F hs h1 hzero hn,zero_mul]

#print axioms nativeCore_actual_source_physical_pairing
end Yamabe3.Analysis.SpherePolar
