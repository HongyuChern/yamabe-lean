import Yamabe3.Analysis.NativeCompactH2GlobalConformalSource
import Yamabe3.Analysis.SmoothCompactSupportedExtension
import Yamabe3.Analysis.NativeH2ChartWeakEquation
import Yamabe3.Analysis.NativeDensityChartSourcePairing

/-! A SAME native completion represented by an actual compact H2
coordinate field on a native test domain has its constructed native
source there, including domains extending beyond the chart. Compact
source support and transposed tests discharge the equation; it is not
an input. This first interface retains measurable coordinate fields. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix ChartOperatorTransfer NativeChartSphereMetric
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

 theorem nativeCompactH2_native_domain_actual_source
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {r R₀:ℝ} (hr:r<R₀) (hKs:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (u:E→ℝ) (hum:Measurable u) (hu:MemWkp 2 2 u univ)
    (hz:∀x:E,x∉closedBall (0:E) r→u x=0)
    (Ω:Set M) (hΩ:IsOpen Ω) (W:H1Zero g.leviCivitaData univ)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict Ω]coordinateExtension e u):
    ∃F_E:Lp ℝ 2 (volume:Measure E),
      (F_E:E→ℝ)=ᵐ[volume]nativeWeakConformalDensity univ gE u ∧
      (W,nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hKs F_E)∈
        nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const Ω:=by
  let K:=closedBall (0:E) R₀
  let K₀:=closedBall (0:E) r
  let B:=ball (0:E) R₀
  have hK₀B:K₀⊆B:=closedBall_subset_ball hr
  have hBK:B⊆K:=ball_subset_closedBall
  have hK₀K:K₀⊆K:=hK₀B.trans hBK
  have hBs:B⊆e.source:=hBK.trans hKs
  have hBc:IsCompact (closure B):=Metric.isCompact_of_isClosed_isBounded isClosed_closure
    ((Metric.isBounded_ball (x:=(0:E)) (r:=R₀)).closure)
  have huB:MemWkp 2 2 u B:=hu.mono_set (by norm_num) isOpen_ball (subset_univ _)
  obtain ⟨F_E,hFE,hDzero⟩:=exists_nativeCompactH2_global_conformal_source gE hu hr hz
  have hDGlobal:∀ᵐx:E∂volume,x∉K₀→nativeWeakConformalDensity univ gE u x=0:=
    (ae_restrict_iff' measurableSet_closedBall.compl).mp hDzero
  have hCoord:coordinateExtension e u=nativeCompactChartFunction e K u:=by
    funext y
    by_cases hy:y∈e.target
    · rw [nativeCompactChartFunction,coordinateExtension_apply e _ hy,coordinateExtension_apply e _ hy]
      by_cases hx:e.symm y∈K
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        exact hz _ (fun h=>hx (hK₀K h))
    · simp only [nativeCompactChartFunction,coordinateExtension,indicator_of_notMem hy]
  refine ⟨F_E,hFE,?_⟩
  intro η hη
  let Pη:M→ℝ:=fun y=>-8*g.leviCivitaData.laplacian η y+g.leviCivitaData.scalarCurvature y*η y
  have hPc:Continuous Pη:=(continuous_const.mul (g.leviCivitaData.contMDiff_laplacian η.smooth).continuous).add
    (g.leviCivitaData.contMDiff_scalarCurvature.continuous.mul η.smooth.continuous)
  have hPzero(y:M)(hy:y∉Ω):Pη y=0:=by
    have hn:y∉tsupport (η:M→ℝ):=fun h=>hy (hη h)
    dsimp only [Pη]
    rw [g.leviCivitaData.laplacian_eq_zero_of_notMem_tsupport hn,image_eq_zero_of_notMem_tsupport hn]
    ring
  have hT:ContDiffOn ℝ ∞ (fun x:E=>η (e x)) B:=by
    intro x hx
    exact (contMDiffAt_iff_contDiffAt.mp (η.smooth.contMDiffAt.comp x
      (he.contMDiffAt (e.open_source.mem_nhds (hBs hx))))).contDiffWithinAt
  obtain ⟨φ,hφ,hφc,hφs,hgerm⟩:=exists_smooth_compact_supported_extension_near_compact isOpen_ball
    (isCompact_closedBall (0:E) r) hK₀B hT
  have hop(x:E)(hx:x∈K₀):nativeConformalDensityTest gE φ x=gE.pullbackVolumeDensity id x*Pη (e x):=by
    dsimp only [nativeConformalDensityTest,Pη]
    rw [laplacian_eq_of_chart_coefficients_and_germ g gE g.leviCivitaData gE.leviCivitaData e he hei
      isOpen_ball hBs (fun x hx=>hcoeff x (hBK hx)) (hK₀B hx) η.smooth.contMDiffAt (hgerm x hx).symm,
      scalarCurvature_eq_of_chart_coefficients g gE g.leviCivitaData gE.leviCivitaData e he
        isOpen_ball hBs (fun x hx=>hcoeff x (hBK hx)) (hK₀B hx), (hgerm x hx).self_of_nhds]
  have hOp:=nativeH2_conformal_transposed_test isOpen_ball hBc gE huB φ hφ hφc hφs
  have hmono:=nativeWeakConformalDensity_mono (D:=B) isOpen_ball (subset_univ _) hu gE
  have hSrc:(∫x in B,nativeWeakConformalDensity B gE u x*φ x)=
      ∫x in K,(F_E:E→ℝ) x*η (e x):=by
    calc
      _=∫x in B,nativeWeakConformalDensity univ gE u x*φ x:=by
        apply integral_congr_ae
        exact hmono.mono (fun x hx=>congrArg (fun t:ℝ=>t*φ x) hx.symm)
      _=∫x in K,nativeWeakConformalDensity univ gE u x*η (e x):=by
        rw [←integral_indicator isOpen_ball.measurableSet,←integral_indicator measurableSet_closedBall]
        apply integral_congr_ae
        filter_upwards [hDGlobal] with x hx
        by_cases hx₀:x∈K₀
        · rw [indicator_of_mem (hK₀B hx₀),indicator_of_mem (hK₀K hx₀)]
          exact congrArg (fun t:ℝ=>nativeWeakConformalDensity univ gE u x*t) (hgerm x hx₀).self_of_nhds
        · have hzero:=hx hx₀
          by_cases hxB:x∈B <;> by_cases hxK:x∈K <;>
            simp [Set.indicator,hxB,hxK,hzero]
      _=_:=by
        apply integral_congr_ae
        exact (ae_restrict_of_ae (s:=K) hFE).mono (fun x hx=>congrArg (fun t:ℝ=>t*η (e x)) hx.symm)
  rw [closedYamabeJacobianForm_test_eq_integral]
  simp only [zero_pow (by decide:(4:ℕ)≠0),mul_zero,zero_mul,sub_zero]
  change (∫y,Pη y*toL2 g.leviCivitaData univ W y ∂g.volumeMeasure)=_
  calc
    _=∫y,nativeCompactChartFunction e K u y*Pη y ∂g.volumeMeasure:=by
      apply integral_congr_ae
      filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mp hrep] with y hy
      by_cases hyΩ:y∈Ω
      · exact (congrArg (fun t:ℝ=>Pη y*t) (hy hyΩ)).trans (by rw [hCoord];ring)
      · rw [hPzero y hyΩ,mul_zero,zero_mul]
    _=∫x in K,u x*Pη (e x)*g.pullbackVolumeDensity e x:=
      integral_nativeCompactChartFunction_mul g e he hei (isCompact_closedBall (0:E) R₀) hKs hum hPc.measurable
    _=∫x in K,u x*nativeConformalDensityTest gE φ x:=by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro x hx
      change u x*Pη (e x)*g.pullbackVolumeDensity e x=u x*nativeConformalDensityTest gE φ x
      by_cases hx₀:x∈K₀
      · rw [hop x hx₀,←pullbackVolumeDensity_eq_of_coefficients g gE e x (hcoeff x hx)]
        ring
      · rw [hz x hx₀,zero_mul,zero_mul,zero_mul]
    _=∫x in B,u x*nativeConformalDensityTest gE φ x:=by
      have hk:(∫x in K,u x*nativeConformalDensityTest gE φ x)=∫x:E,u x*nativeConformalDensityTest gE φ x:=by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [hz x (fun h=>hx (hK₀K h)),zero_mul]
      have hb:(∫x in B,u x*nativeConformalDensityTest gE φ x)=∫x:E,u x*nativeConformalDensityTest gE φ x:=by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [hz x (fun h=>hx (hK₀B h)),zero_mul]
      exact hk.trans hb.symm
    _=_:=hOp.trans (hSrc.trans (nativeDensityChartSourceCLM_pairing g gE e he hei
      (isCompact_closedBall (0:E) R₀) hKs hcoeff F_E η).symm)

#print axioms nativeCompactH2_native_domain_actual_source
end Yamabe3.Analysis.SpherePolar
