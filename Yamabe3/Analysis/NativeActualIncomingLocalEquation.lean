import Yamabe3.Analysis.NativeActualIncomingSmoothField
import Yamabe3.Analysis.NativeJacobianC2
import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import Yamabe3.Analysis.NativeHomogeneousH4Return
import Yamabe3.Analysis.NativeOriginalAffineFeedback
import Yamabe3.Analysis.NativeH4InnerPartialFeedback
import Yamabe3.Analysis.NativeH4SupportedWindowSource

/-! The ACTUAL affine original-source feedback has the required inner
fixed point, since its incoming source has exactly zero first coordinate.
This discharges the partial inner cancellation premise without assuming
an obsolete full-collar exterior fixed point. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic GreenParametrix ChartOperatorTransfer PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
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


theorem nativeActualIncoming_smooth_local_operator_zero
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
    (F:E→ℝ) (hF:ContDiff ℝ ∞ F)
    (hrep:∀x∈closedBall (0:E) 4,F=ᶠ[𝓝 x]
      (fun y=>nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const W.open_domain R (e (a • y))))
    {x:E} (hx:x∈closedBall (0:E) 4):
    principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x+
      a^2*nativePotentialDensity gE (a • x)*F x=0:=by
  let ΩE:=ball (0:E) (a*64)
  let U:=nativeHomogeneousEnergyRepresentative g (fun _:M=>0) contMDiff_const W.open_domain R
  have hU:=nativeHomogeneousEnergyRepresentative_spec g (fun _:M=>0) contMDiff_const W.open_domain R
  have hsourceE:ΩE⊆e.source:=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall W.receiving_fit).trans hsource)
  have hcx:∀y∈ΩE,gE.euclideanCoefficients y=g.pullbackCoefficients e y:=
    fun y hy=>hcoeff y ((closedBall_subset_closedBall W.receiving_fit) (ball_subset_closedBall hy))
  have hxE:a • x∈ΩE:=by
    rw [mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg ha.le]
    have hn:=mem_closedBall_zero_iff.mp hx
    nlinarith
  have hhum:ContMDiffAt (𝓡 3) 𝓘(ℝ,ℝ) ∞ U (e (a • x)):=
    hU.1.contMDiffAt (W.open_domain.mem_nhds (mem_image_of_mem e hxE))
  have hphys:(fun z:E=>F (a⁻¹ • z))=ᶠ[𝓝 (a • x)](fun z=>U (e z)):=by
    have heq: a⁻¹ • (a • x)=x:=by rw [smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    have ht:Tendsto (fun z:E=>a⁻¹ • z) (𝓝 (a • x)) (𝓝 x):=by
      simpa only [heq] using (continuous_const_smul a⁻¹).tendsto (a • x)
    have hh:=(hrep x hx).comp_tendsto ht
    filter_upwards [hh] with z hz
    change F (a⁻¹ • z)=U (e (a • (a⁻¹ • z))) at hz
    simpa only [smul_smul,mul_inv_cancel₀ ha.ne',one_smul] using hz
  have hlap:=laplacian_eq_of_chart_coefficients_and_germ g gE g.leviCivitaData gE.leviCivitaData
    e he hei (show IsOpen ΩE from isOpen_ball) hsourceE hcx hxE hhum hphys.symm
  have hRc:=scalarCurvature_eq_of_chart_coefficients g gE g.leviCivitaData gE.leviCivitaData
    e he (show IsOpen ΩE from isOpen_ball) hsourceE hcx hxE
  have hv:F x=U (e (a • x)):=(hrep x hx).self_of_nhds
  have hz:=hU.2.2 (e (a • x)) (mem_image_of_mem e hxE)
  simp only [zero_pow (by decide:(4:ℕ)≠0),mul_zero,sub_zero] at hz
  let H:E→ℝ:=fun z=>F (a⁻¹ • z)
  have hH:ContDiffAt ℝ 2 H (a • x):=
    ((hF.comp (contDiff_id.const_smul a⁻¹)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hscale:principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) F x=
      a^2*principalSource (nativeDivergenceMatrix gE) H (a • x):=by
    have hh:=principalSource_scaled_centered (nativeDivergenceMatrix gE) H a 1 0 x
    simpa only [H,smul_smul,inv_mul_cancel₀ ha.ne',one_smul,sub_zero,one_mul] using hh
  calc
    _ = (a^2*gE.pullbackVolumeDensity id (a • x)/8)*
        (-8*g.leviCivitaData.laplacian U (e (a • x))+
          g.leviCivitaData.scalarCurvature (e (a • x))*U (e (a • x))):=by
      rw [hscale,native_principalSource_eq_negative_density_laplacian_C2 gE gE.leviCivitaData hH]
      unfold nativePotentialDensity
      change a^2*(-gE.pullbackVolumeDensity id (a • x)*gE.leviCivitaData.laplacian H (a • x))+_= _
      rw [hlap,hRc,hv]
      ring
    _ = 0:=by rw [hz,mul_zero]

#print axioms nativeActualIncoming_smooth_local_operator_zero
end Yamabe3.Analysis.SpherePolar
