import Yamabe3.Analysis.NativeH2ConformalTransposed
import Yamabe3.Analysis.NativeCompactClosedJetSourcePair
import Yamabe3.Analysis.NativeJacobianLocality

/-! Local actual H2 coordinate equations become the closed native H1
equation for the SAME native volume class. The local representation and
source identities are explicit intermediate premises; downstream actual
field producers must discharge them. No existence claim is made here. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix ChartOperatorTransfer NativeChartSphereMetric
open PoincareMT.LeviCivitaData.Dirichlet Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeH2_chart_closed_weak_equation
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O:Set E} (hO:IsOpen O) (hOc:IsCompact (closure O)) (hOs:closure O⊆e.source)
    (hcoeff:∀x∈O,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (u:E→ℝ) (hum:Measurable u) (hu:MemWkp 2 2 u O)
    (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' O)]
      nativeCompactChartFunction e (closure O) u)
    (hsource:nativeWeakConformalDensity O gE u=ᵐ[volume.restrict O]
      fun x=>gE.pullbackVolumeDensity id x*(F:M→ℝ) (e x)) :
    (W,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' O) := by
  intro φ hs
  have hΩ:IsOpen (e '' O):=e.isOpen_image_of_subset_source hO (subset_closure.trans hOs)
  have hφt:tsupport (φ:M→ℝ)⊆e.target:=by
    intro y hy
    obtain ⟨x,hx,rfl⟩:=hs hy
    exact e.map_source (hOs (subset_closure hx))
  let ψ:=chartPullback e (φ:M→ℝ)
  have hψ:ContDiff ℝ ∞ ψ:=contDiff_chartPullback e he φ.smooth φ.hasCompactSupport hφt
  have hψc:HasCompactSupport ψ:=hasCompactSupport_chartPullback e φ.hasCompactSupport hφt
  have hψs:tsupport ψ⊆O:=by
    intro x hx
    obtain ⟨y,hy,rfl⟩:=tsupport_chartPullback_subset_image e φ.hasCompactSupport hφt hx
    obtain ⟨z,hz,rfl⟩:=hs hy
    simpa only [e.left_inv (hOs (subset_closure hz))] using hz
  let Pφ:M→ℝ:=fun y=>-8*g.leviCivitaData.laplacian φ y+g.leviCivitaData.scalarCurvature y*φ y
  have hPc:Continuous Pφ:=
    (continuous_const.mul (g.leviCivitaData.contMDiff_laplacian φ.smooth).continuous).add
      (g.leviCivitaData.contMDiff_scalarCurvature.continuous.mul φ.smooth.continuous)
  have hPzero(y:M)(hy:y∉e '' O):Pφ y=0:=by
    have hn:y∉tsupport (φ:M→ℝ):=fun h=>hy (hs h)
    dsimp only [Pφ]
    rw [g.leviCivitaData.laplacian_eq_zero_of_notMem_tsupport hn,image_eq_zero_of_notMem_tsupport hn]
    ring
  have hxφ(x:E)(hx:x∈closure O\O):φ (e x)=0 ∧ Pφ (e x)=0:=by
    have hn:e x∉e '' O:=by
      rintro ⟨z,hz,hez⟩
      have hxz:x=z:=e.injOn (hOs hx.1) (hOs (subset_closure hz)) hez.symm
      exact hx.2 (hxz ▸ hz)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h=>hn (hs h)),hPzero _ hn⟩
  have hop(x:E)(hx:x∈O):nativeConformalDensityTest gE ψ x=
      gE.pullbackVolumeDensity id x*Pφ (e x):=by
    dsimp only [nativeConformalDensityTest,Pφ,ψ]
    rw [laplacian_eq_of_chart_coefficients_and_germ g gE g.leviCivitaData gE.leviCivitaData
      e he hei hO (subset_closure.trans hOs) hcoeff hx φ.smooth.contMDiffAt
      (chartPullback_eventuallyEq e (φ:M→ℝ) (hOs (subset_closure hx))).symm,
      scalarCurvature_eq_of_chart_coefficients g gE g.leviCivitaData gE.leviCivitaData
        e he hO (subset_closure.trans hOs) hcoeff hx,
      chartPullback_apply e (φ:M→ℝ) (hOs (subset_closure hx))]
  have hFpair:inner ℝ F (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))=
      ∫x in O,nativeWeakConformalDensity O gE u x*ψ x:=by
    rw [L2.inner_def,toL2_coe]
    calc
      _ = ∫y,(F:M→ℝ) y*φ y ∂g.volumeMeasure:=by
        apply integral_congr_ae
        filter_upwards [φ.memLp.coeFn_toLp] with y hy
        simp only [Real.inner_apply]
        change (F:M→ℝ) y*(φ.memLp.toLp φ) y=_
        rw [hy]
      _ = ∫y in e '' closure O,(F:M→ℝ) y*φ y ∂g.volumeMeasure:=by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        rw [image_eq_zero_of_notMem_tsupport (fun h=>hy ((image_mono subset_closure) (hs h))),mul_zero]
      _ = ∫x in closure O,(F:M→ℝ) (e x)*φ (e x)*g.pullbackVolumeDensity e x:=
        integral_compact_image_eq_pullback_density (g:=g) e he hei hOc hOs
          ((Lp.stronglyMeasurable F).measurable.mul φ.smooth.continuous.measurable)
      _ = ∫x in O,(F:M→ℝ) (e x)*φ (e x)*g.pullbackVolumeDensity e x:=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hOc.measurableSet subset_closure
          (fun x hx=>by rw [(hxφ x hx).1,mul_zero,zero_mul])
      _ = _:=by
        apply integral_congr_ae
        filter_upwards [hsource,ae_restrict_mem hO.measurableSet] with x hx hxO
        simp only [ψ,Function.comp_apply]
        rw [hx,chartPullback_apply e (φ:M→ℝ) (hOs (subset_closure hxO)),
          ←pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x hxO)]
        ring
  rw [closedYamabeJacobianForm_test_eq_integral,hFpair]
  simp only [zero_pow (by decide:(4:ℕ)≠0),mul_zero,zero_mul,sub_zero]
  calc
    _ = ∫y,Pφ y*nativeCompactChartFunction e (closure O) u y ∂g.volumeMeasure:=by
      apply integral_congr_ae
      filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mp hrep] with y hy
      change Pφ y*toL2 g.leviCivitaData univ W y=_
      by_cases hyΩ:y∈e '' O
      · rw [hy hyΩ]
      · rw [hPzero y hyΩ,zero_mul,zero_mul]
    _ = ∫y,nativeCompactChartFunction e (closure O) u y*Pφ y ∂g.volumeMeasure:=by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y=>mul_comm _ _)
    _ = ∫x in closure O,u x*Pφ (e x)*g.pullbackVolumeDensity e x:=
      integral_nativeCompactChartFunction_mul g e he hei hOc hOs hum hPc.measurable
    _ = ∫x in O,u x*Pφ (e x)*g.pullbackVolumeDensity e x:=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hOc.measurableSet subset_closure
        (fun x hx=>by rw [(hxφ x hx).2,mul_zero,zero_mul])
    _ = ∫x in O,u x*nativeConformalDensityTest gE ψ x:=by
      apply setIntegral_congr_fun hO.measurableSet
      intro x hx
      dsimp only
      rw [hop x hx,←pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x hx)]
      ring
    _ = _:=nativeH2_conformal_transposed_test hO hOc gE hu ψ hψ hψc hψs

#print axioms nativeH2_chart_closed_weak_equation
end Yamabe3.Analysis.SpherePolar
