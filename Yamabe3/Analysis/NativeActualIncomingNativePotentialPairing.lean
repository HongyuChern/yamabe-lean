import Yamabe3.Analysis.NativeFullBubbleNativePotential
import Yamabe3.Analysis.NativeDensityChartSourcePairing
import Yamabe3.Analysis.NativeActualIncomingPhysicalPairing

/-! The normalized incoming potential pairing is EXACTLY the actual
native full-minus-tail reaction of the SAME return. Density, 3D volume,
core, unit/physical radii and the factor8a are checked pointwise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic SphereSpectrum Delaunay NativeChartSphereMetric PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable {g:RiemannianMetric 3 M} {gE:RiemannianMetric 3 E} {e:OpenPartialHomeomorph E M}
  {he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source}
  {hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target}
  {R₀:ℝ} {hsource:closedBall (0:E) R₀⊆e.source}
  {P:NativeHighPotential}
  {hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ}
  {v:ℝ→ℝ} {hv:Continuous v} {hb:∀t,0 ≤ v t ∧ v t ≤ 1}
  {τ cTail:ℝ} {ht:0 < τ} {m n:ℕ} {b S CR CM:ℝ}
  {χin χout:E→ℝ} {hχin:ContDiff ℝ ∞ χin} {hχout:ContDiff ℝ ∞ χout}
  {a:ℝ} {ha:0 < a} {ha1:a ≤ 1}
  (W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
    (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
    (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
    (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1)


theorem nativeActualIncoming_potential_native_pairing
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hfit:a*(Real.exp cTail+1)≤R₀)
    (R:H1Zero g.leviCivitaData univ) (η:EnergyTest g.leviCivitaData univ):
    8*a*(∫x in ball (0:E) (Real.exp cTail+1),nativeIncomingPotentialCoefficient gE a τ cTail χin x*
      toL2 g.leviCivitaData univ R (e (a • x))*η (e (a • x)))=
    ∫y,8*(nativeCompactChartFunction e (closedBall (0:E) R₀) (fullBubbleScaledTail τ cTail (Real.log a)) y-
      nativeScaledFullBubblePotential e (closedBall (0:E) R₀) τ a y)*
      (1-W.core y)*toL2 g.leviCivitaData univ R y*η y ∂g.volumeMeasure:=by
  let K:=closedBall (0:E) R₀
  let O:=ball (0:E) (Real.exp cTail+1)
  let d:E→ℝ:=fun x=>fullBubblePotentialTail τ (Real.exp cTail) x-fullBubbleSpatialPotential (Real.exp τ) x
  let p:M→ℝ:=fun y=>(1-W.core y)*toL2 g.leviCivitaData univ R y*η y
  let H:E→ℝ:=fun x=>nativeIncomingPotentialCoefficient gE a τ cTail χin x*
    toL2 g.leviCivitaData univ R (e (a • x))*η (e (a • x))
  have hd:Measurable d:=((fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.measurable.indicator
    (measurableSet_lt (measurable_const (a:=Real.exp cTail)) measurable_norm)).sub
      (fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.measurable
  have hf:Measurable (fun x:E=>(a⁻¹)^2*d (a⁻¹ • x)):=
    (hd.comp (continuous_const_smul a⁻¹).measurable).const_mul _
  have hp:Measurable p:=((measurable_const.sub W.core.smooth.continuous.measurable).mul
    (Lp.stronglyMeasurable (toL2 g.leviCivitaData univ R)).measurable).mul η.smooth.continuous.measurable
  have hOz(x:E)(hx:x∉O):H x=0:=by
    have hn:Real.exp cTail<‖x‖:=by
      have hh:Real.exp cTail+1≤‖x‖:=not_lt.mp (fun h=>hx (mem_ball_zero_iff.mpr h))
      linarith
    dsimp only [H]
    rw [nativeIncomingPotentialCoefficient_zero_outer gE a τ cTail χin hn,zero_mul,zero_mul]
  have hOK:euclideanDilatedDomain a O⊆K:=euclideanDilatedBall_subset_closedBall ha hfit
  have hscale(x:E)(hx:x∈K):
      ((a⁻¹)^2*d (a⁻¹ • x))*p (e x)*g.pullbackVolumeDensity e x=(a⁻¹)^2*H (a⁻¹ • x):=by
    have hxS:=hsource hx
    have hx':a • (a⁻¹ • x)=x:=by rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    have hc:W.core (e x)=χin (a⁻¹ • x):=by
      simpa only [hx'] using W.core_value (a⁻¹ • x) (by simpa only [hx'] using hxS)
    dsimp only [d,p,H,nativeIncomingPotentialCoefficient]
    rw [hx',hc,←pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x hx)]
    ring
  have hwhole:(∫x in K,H (a⁻¹ • x))=∫x:E,H (a⁻¹ • x):=by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply hOz
    exact fun h=>hx (hOK h)
  symm
  calc
    _=8*(∫y,nativeCompactChartFunction e K (fun x:E=>(a⁻¹)^2*d (a⁻¹ • x)) y*p y ∂g.volumeMeasure):=by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      have hdiff:=congrFun (nativeBubbleTail_minus_full e K ha τ cTail) y
      change nativeCompactChartFunction e K (fullBubbleScaledTail τ cTail (Real.log a)) y-
        nativeScaledFullBubblePotential e K τ a y=
        nativeCompactChartFunction e K (fun x:E=>(a⁻¹)^2*d (a⁻¹ • x)) y at hdiff
      change 8*(nativeCompactChartFunction e K (fullBubbleScaledTail τ cTail (Real.log a)) y-
        nativeScaledFullBubblePotential e K τ a y)*(1-W.core y)*toL2 g.leviCivitaData univ R y*η y=_
      rw [hdiff]
      dsimp only [p]
      ring
    _=8*(∫x in K,((a⁻¹)^2*d (a⁻¹ • x))*p (e x)*g.pullbackVolumeDensity e x):=by
      rw [integral_nativeCompactChartFunction_mul g e he hei (isCompact_closedBall (0:E) R₀) hsource hf hp]
    _=8*(a⁻¹)^2*(∫x in K,H (a⁻¹ • x)):=by
      calc
        _=8*(∫x in K,(a⁻¹)^2*H (a⁻¹ • x)):=by
          congr 1
          exact setIntegral_congr_fun (isCompact_closedBall (0:E) R₀).measurableSet hscale
        _=_:=by rw [integral_const_mul];ring
    _=8*(a⁻¹)^2*(a^3*(∫x:E,H x)):=by
      rw [hwhole]
      have hdil:=setIntegral_comp_dilation (inv_ne_zero ha.ne') (univ:Set E) H
      simp only [preimage_univ,Measure.restrict_univ,finrank_euclideanSpace_fin,inv_pow,inv_inv,
        abs_of_nonneg (pow_nonneg ha.le 3)] at hdil
      rw [hdil]
    _=8*a*(∫x in O,H x):=by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hOz]
      field_simp [ha.ne']
      <;>ring

#print axioms nativeActualIncoming_potential_native_pairing
end Yamabe3.Analysis.SpherePolar
