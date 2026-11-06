import Yamabe3.Analysis.NativeJacobianC2
import Yamabe3.Analysis.Green.NativeChartOperatorTransfer
import Yamabe3.Analysis.EuclideanEnergyDilation

/-! Exact native operator transport for one smooth test, before source
pairings. The same physical dilation, native density and coefficient8
are retained, including at the center; no radial potential is introduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix ChartOperatorTransfer PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeScaledSmoothTest_operator_identity
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hKs:K⊆e.source)
    (hcoeff:∀x∈K,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {a:ℝ} (ha:0<a) {O:Set E} (hO:IsOpen O) (hfit:euclideanDilatedDomain a O⊆K)
    (ψ:EnergyTest g.leviCivitaData univ) (Φ:E→ℝ) (hΦ:ContDiff ℝ ∞ Φ)
    (hrep:∀x∈O,Φ=ᶠ[𝓝 x](fun y=>ψ (e (a • y)))) {x:E} (hx:x∈O):
    principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) Φ x+
      a^2*nativePotentialDensity gE (a • x)*Φ x=
        (a^2*gE.pullbackVolumeDensity id (a • x)/8)*
          (-8*g.leviCivitaData.laplacian ψ (e (a • x))+
            g.leviCivitaData.scalarCurvature (e (a • x))*ψ (e (a • x))):=by
  let D:=euclideanDilatedDomain a O
  have hD:IsOpen D:=hO.preimage (continuous_const_smul a⁻¹)
  have hxD:a • x∈D:=by
    change a⁻¹ • (a • x)∈O
    simpa only [smul_smul,inv_mul_cancel₀ ha.ne',one_smul] using hx
  let H:E→ℝ:=fun z=>Φ (a⁻¹ • z)
  have hphys:H=ᶠ[𝓝 (a • x)](ψ ∘ e):=by
    have heq:a⁻¹ • (a • x)=x:=by rw [smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    have ht:Tendsto (fun z:E=>a⁻¹ • z) (𝓝 (a • x)) (𝓝 x):=by
      simpa only [heq] using (continuous_const_smul a⁻¹).tendsto (a • x)
    filter_upwards [(hrep x hx).comp_tendsto ht] with z hz
    change Φ (a⁻¹ • z)=ψ (e (a • (a⁻¹ • z))) at hz
    simpa only [H,Function.comp_apply,smul_smul,mul_inv_cancel₀ ha.ne',one_smul] using hz
  have hlap:=laplacian_eq_of_chart_coefficients_and_germ g gE g.leviCivitaData gE.leviCivitaData e he hei
    hD (hfit.trans hKs) (fun y hy=>hcoeff y (hfit hy)) hxD ψ.smooth.contMDiffAt hphys.symm
  have hRc:=scalarCurvature_eq_of_chart_coefficients g gE g.leviCivitaData gE.leviCivitaData e he
    hD (hfit.trans hKs) (fun y hy=>hcoeff y (hfit hy)) hxD
  have hv:Φ x=ψ (e (a • x)):=(hrep x hx).self_of_nhds
  have hH:ContDiffAt ℝ 2 H (a • x):=
    ((hΦ.comp (contDiff_id.const_smul a⁻¹)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hscale:principalSource (fun y=>nativeDivergenceMatrix gE (a • y)) Φ x=
      a^2*principalSource (nativeDivergenceMatrix gE) H (a • x):=by
    have hh:=principalSource_scaled_centered (nativeDivergenceMatrix gE) H a 1 0 x
    simpa only [H,smul_smul,inv_mul_cancel₀ ha.ne',one_smul,sub_zero,one_mul] using hh
  rw [hscale,native_principalSource_eq_negative_density_laplacian_C2 gE gE.leviCivitaData hH]
  unfold nativePotentialDensity
  rw [hlap,hRc,hv]
  ring

#print axioms nativeScaledSmoothTest_operator_identity
end Yamabe3.Analysis.SpherePolar
