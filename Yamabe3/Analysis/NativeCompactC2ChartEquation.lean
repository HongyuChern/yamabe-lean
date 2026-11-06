import Yamabe3.Analysis.NativeCompactConformalEquation
import Yamabe3.Analysis.NativeDensityChartSourcePairing
import Yamabe3.Analysis.Green.NativeChartTestExtension

/-! Actual chart transfer of the compact C2 conformal equation. The
coordinate test is constructed with a genuine compact smooth extension.
All operator comparisons take place in matching chart germs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix ChartOperatorTransfer NativeChartSphereMetric
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

theorem nativeC2Cutoff_conformal_zero_off_support (g:RiemannianMetric 3 E)
    {χ:E→ℝ} (hχ:ContDiff ℝ ∞ χ) (u:nativeC2OffZero) {x:E} (hx:x∉tsupport χ) :
    -8*g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
      g.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x=0 := by
  have he:(nativeC2Cutoff χ hχ u).val=ᶠ[𝓝 x](fun _=>0):=by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    change χ y*u.val y=0
    rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
  have hΔ:g.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x=0:=by
    rw [g.leviCivitaData.laplacian_eq_of_eventuallyEq he]
    simpa only [zero_mul] using g.leviCivitaData.laplacian_const_mul 0 (fun _:E=>0) x
  rw [hΔ,he.self_of_nhds]
  ring

theorem nativeCompactC2_chart_conformal_equation
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K U:Set E} (hK:IsCompact K) (hKU:K⊆U) (hU:IsOpen U) (hUs:U⊆e.source)
    (hcoeff:∀x∈U,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆nativePoissonEntranceCollar) (hχK:tsupport χ⊆K)
    {r:ℝ} (hr:0<r) (hrs:closedBall (0:E) r⊆e.source)
    (β:ContDiffBump (0:E)) (hβ:β.rOut<r) (hχβ:tsupport χ⊆tsupport β)
    (u:nativeC2OffZero) (φ:EnergyTest g.leviCivitaData univ) :
    (∫y,(-8*g.leviCivitaData.laplacian φ y+g.leviCivitaData.scalarCurvature y*φ y)*
      nativeCompactChartFunction e K (nativeC2Cutoff χ hχ u).val y ∂g.volumeMeasure)=
      ∫x in K,gE.pullbackVolumeDensity id x*
        (-8*gE.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
          gE.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x)*φ (e x) := by
  obtain ⟨ψ,hψ,hψc,_,hψg,_⟩:=Yamabe3.Parametrix.exists_compact_chart_test e he hei hr hrs β hβ φ.smooth
  have hKs:K⊆e.source:=hKU.trans hUs
  have hpc:Continuous (fun y=>-8*g.leviCivitaData.laplacian φ y+g.leviCivitaData.scalarCurvature y*φ y):=
    (continuous_const.mul (g.leviCivitaData.contMDiff_laplacian φ.smooth).continuous).add
      (g.leviCivitaData.contMDiff_scalarCurvature.continuous.mul φ.smooth.continuous)
  have hψop (x:E) (hx:x∈tsupport χ) :
      -8*gE.leviCivitaData.laplacian ψ x+gE.leviCivitaData.scalarCurvature x*ψ x=
        -8*g.leviCivitaData.laplacian φ (e x)+g.leviCivitaData.scalarCurvature (e x)*φ (e x) := by
    have hxU:=hKU (hχK hx)
    rw [laplacian_eq_of_chart_coefficients_and_germ g gE g.leviCivitaData gE.leviCivitaData
      e he hei hU hUs hcoeff hxU φ.smooth.contMDiffAt (hψg x (hχβ hx)).symm,
      scalarCurvature_eq_of_chart_coefficients g gE g.leviCivitaData gE.leviCivitaData e he hU hUs hcoeff hxU,
      (hψg x (hχβ hx)).self_of_nhds]
    rfl
  calc
    _ = ∫y,nativeCompactChartFunction e K (nativeC2Cutoff χ hχ u).val y*
        (-8*g.leviCivitaData.laplacian φ y+g.leviCivitaData.scalarCurvature y*φ y) ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x=>mul_comm _ _)
    _ = ∫x in K,(nativeC2Cutoff χ hχ u).val x*
        (-8*g.leviCivitaData.laplacian φ (e x)+g.leviCivitaData.scalarCurvature (e x)*φ (e x))*g.pullbackVolumeDensity e x :=
      integral_nativeCompactChartFunction_mul g e he hei hK hKs
        (nativeC2Cutoff_global_C2 hχ hs u).continuous.measurable hpc.measurable
    _ = ∫x in K,(nativeC2Cutoff χ hχ u).val x*
        (-8*gE.leviCivitaData.laplacian ψ x+gE.leviCivitaData.scalarCurvature x*ψ x)*gE.pullbackVolumeDensity id x := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      by_cases hxχ:x∈tsupport χ
      · rw [hψop x hxχ,pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x (hKU hx))]
      · have hz:(nativeC2Cutoff χ hχ u).val x=0:=by
          change χ x*u.val x=0
          rw [image_eq_zero_of_notMem_tsupport hxχ,zero_mul]
        simp only [hz,zero_mul]
    _ = ∫x,(nativeC2Cutoff χ hχ u).val x*
        (-8*gE.leviCivitaData.laplacian ψ x+gE.leviCivitaData.scalarCurvature x*ψ x) ∂gE.volumeMeasure := by
      rw [native_integral_eq_density]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz:χ x=0:=image_eq_zero_of_notMem_tsupport (fun h=>hx (hχK h))
      change (χ x*u.val x)*_*_=0
      rw [hz,zero_mul,zero_mul,zero_mul]
    _ = ∫x,(-8*gE.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
        gE.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x)*ψ x ∂gE.volumeMeasure :=
      nativeC2Cutoff_conformal_transposed gE hχ hc hs u ψ hψ hψc
    _ = ∫x in K,(-8*gE.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
        gE.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x)*ψ x*gE.pullbackVolumeDensity id x := by
      rw [native_integral_eq_density]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [nativeC2Cutoff_conformal_zero_off_support gE hχ u (fun h=>hx (hχK h)),zero_mul,zero_mul]
    _ = _ := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp only
      by_cases hxχ:x∈tsupport χ
      · rw [(hψg x (hχβ hxχ)).self_of_nhds]
        simp only [Function.comp_apply]
        ring
      · rw [nativeC2Cutoff_conformal_zero_off_support gE hχ u hxχ]
        ring

#print axioms nativeC2Cutoff_conformal_zero_off_support
#print axioms nativeCompactC2_chart_conformal_equation
end Yamabe3.Analysis.SpherePolar
