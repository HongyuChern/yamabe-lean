import Yamabe3.Analysis.NativeFullBubbleNativePotential
import Yamabe3.Analysis.NativeDensityPhysicalShellPairing
import Yamabe3.Analysis.NativeGlobalOperatorTestIntegrability

/-! The SAME completed native volume class has the exact full-bubble
reaction pairing. Actual raw-source L2 transport avoids any pointwise
restriction of a volume a.e. identity to the boundary. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay GreenParametrix PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 theorem nativeFullBubble_whole_domain_completion_pairing
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (R₀:ℝ) (hKs:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {a:ℝ} (ha:0<a) (τ:ℝ) (u:E→ℝ) (hu:MemLp u 2 (volume:Measure E))
    (Q:H1Zero g.leviCivitaData univ)
    (Ω:Set M) (hΩ:IsOpen Ω)
    (hrep:(toL2 g.leviCivitaData univ Q:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]
      coordinateExtension e (fun y:E=>u (a⁻¹ • y)))
    (η:EnergyTest g.leviCivitaData univ) (hη:tsupport (η:M→ℝ)⊆Ω)
    (φ:E→ℝ) (htest:∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y))
    (hzero:∀y:E,y∉closedBall (0:E) R₀→u (a⁻¹ • y)=0):
    (∫y,8*nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y*
      toL2 g.leviCivitaData univ Q y*η y ∂g.volumeMeasure)=
      8*a*(∫x:E,gE.pullbackVolumeDensity id (a • x)*
        nativeHalfEndPotentialCoefficient (fullBubblePhasePotential τ) x*u x*φ x):=by
  let K:=closedBall (0:E) R₀
  let f:E→ℝ:=fun x=>(a⁻¹)^2*fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)
  let U:E→ℝ:=fun x=>u (a⁻¹ • x)
  let c:E→ℝ:=fun x=>8*gE.pullbackVolumeDensity id x*f x
  let F:E→ℝ:=K.indicator (fun x=>c x*U x)
  have hfc:Continuous f:=continuous_const.mul ((fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.comp (continuous_const_smul _))
  have hc:Continuous c:=(continuous_const.mul (native_density_smooth_positive gE).1.continuous).mul hfc
  have hcLp:MemLp c ⊤ (volume.restrict K):=continuousOn_compact_memLp_top (isCompact_closedBall (0:E) R₀) hc.continuousOn
  have hU:MemLp U 2 (volume:Measure E):=by
    simpa only [preimage_univ,Measure.restrict_univ] using memLp_comp_dilation (inv_ne_zero ha.ne') (hu.restrict univ)
  have hRaw:MemLp F 2 (volume:Measure E):=by
    apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
    apply ((hU.restrict K).mul' hcLp).ae_eq
    exact Eventually.of_forall fun x=>by dsimp only [c,Pi.mul_apply]
  have hRawNative(y:M):nativeDensityCorrectedChartSource gE e K F y=
      8*nativeScaledFullBubblePotential e K τ a y*coordinateExtension e U y:=by
    by_cases hy:y∈e.target
    · simp only [nativeDensityCorrectedChartSource,nativeScaledFullBubblePotential,nativeCompactChartFunction,
        coordinateExtension_apply e _ hy]
      by_cases hx:e.symm y∈K
      · simp only [F,indicator_of_mem hx]
        dsimp only [c,f]
        field_simp [(native_density_smooth_positive gE).2 (e.symm y) |>.ne',ha.ne'] <;> ring
      · simp only [F,indicator_of_notMem hx,zero_div,zero_mul,mul_zero]
    · simp only [nativeDensityCorrectedChartSource,nativeScaledFullBubblePotential,nativeCompactChartFunction,
        coordinateExtension,indicator_of_notMem hy,zero_mul,mul_zero]
  have hRepGlobal:∀ᵐy:M∂g.volumeMeasure,y∈Ω→
      toL2 g.leviCivitaData univ Q y=coordinateExtension e U y:=
    (ae_restrict_iff' hΩ.measurableSet).mp hrep
  calc
    _=∫y,nativeDensityCorrectedChartSource gE e K F y*η y ∂g.volumeMeasure:=by
      apply integral_congr_ae
      filter_upwards [hRepGlobal] with y hy
      rw [hRawNative]
      by_cases hyt:y∈Ω
      · exact congrArg (fun r:ℝ=>8*nativeScaledFullBubblePotential e K τ a y*r*η y) (hy hyt)
      · have hyη:η y=0:=image_eq_zero_of_notMem_tsupport (fun h=>hyt (hη h))
        rw [hyη,mul_zero,mul_zero]
    _=∫x in K,F x*η (e x):=nativeDensityCorrectedSource_actual_pairing g gE e he hei
      (isCompact_closedBall (0:E) R₀) hKs hcoeff hRaw η
    _=∫x in K,(8*(a⁻¹)^2)*(gE.pullbackVolumeDensity id x*
      fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)*u (a⁻¹ • x)*φ (a⁻¹ • x)):=by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro x hx
      change F x*η (e x)=_
      rw [show F x=c x*U x from indicator_of_mem hx _,←htest x hx]
      dsimp only [c,f,U]
      ring
    _=∫x:E,(8*(a⁻¹)^2)*(gE.pullbackVolumeDensity id x*
      fullBubbleSpatialPotential (Real.exp τ) (a⁻¹ • x)*u (a⁻¹ • x)*φ (a⁻¹ • x)):=by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp only [hzero x hx,mul_zero,zero_mul]
    _=(8*(a⁻¹)^2)*(a^3*(∫z:E,gE.pullbackVolumeDensity id (a • z)*
      fullBubbleSpatialPotential (Real.exp τ) z*u z*φ z)):=by
      rw [integral_const_mul]
      have hd:=setIntegral_comp_dilation (inv_ne_zero ha.ne') (univ:Set E)
        (fun z:E=>gE.pullbackVolumeDensity id (a • z)*fullBubbleSpatialPotential (Real.exp τ) z*u z*φ z)
      simp only [preimage_univ,Measure.restrict_univ,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,
        finrank_euclideanSpace_fin,inv_pow,inv_inv,abs_of_nonneg (pow_nonneg ha.le 3)] at hd
      rw [hd]
    _=8*a*(∫z:E,gE.pullbackVolumeDensity id (a • z)*fullBubbleSpatialPotential (Real.exp τ) z*u z*φ z):=by
      field_simp [ha.ne'] <;> ring
    _=_:=by
      congr 1
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (0:E)] with x hx
      rw [nativeHalfEnd_fullBubble_spatial_eq τ hx]

#print axioms nativeFullBubble_whole_domain_completion_pairing
end Yamabe3.Analysis.SpherePolar
