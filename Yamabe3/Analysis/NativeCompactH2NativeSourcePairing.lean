import Yamabe3.Analysis.NativeCompactH2GlobalConformalSource
import Yamabe3.Analysis.NativeDensityChartSourcePairing

/-! The actually constructed native L2 source has the exact physical
weak-operator pairing of the SAME unit H2 field. Chart support, test
identity, density and factor8a are all explicit and proved. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Manifold Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

 theorem nativeCompactH2_native_source_physical_pairing
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (R₀:ℝ) (hKs:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {a:ℝ} (ha:0<a) (u:E→ℝ) (hu:MemWkp 2 2 u univ)
    (F_E:Lp ℝ 2 (volume:Measure E))
    (hF:(F_E:E→ℝ)=ᵐ[volume]nativeWeakConformalDensity univ gE (fun y:E=>u (a⁻¹ • y)))
    (η:EnergyTest g.leviCivitaData univ) (φ:E→ℝ)
    (htest:∀y∈closedBall (0:E) R₀,φ (a⁻¹ • y)=η (e y))
    (hzero:∀y:E,y∉closedBall (0:E) R₀→u (a⁻¹ • y)=0):
    inner ℝ (nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hKs F_E)
      (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ))=
      8*a*(∫x:E,nativeWeakRescaledDelaunayJacobian univ gE a (fun _=>0) 0 u x*φ x):=by
  have hU:MemWkp 2 2 (fun y:E=>u (a⁻¹ • y)) univ:=by
    simpa only [preimage_univ] using memWkp_comp_dilation (inv_ne_zero ha.ne') isOpen_univ
      (by norm_num:(1:ℝ≥0∞)≤2) 2 hu
  have hzD:=nativeGlobalConformalDensity_zero_on_open gE hU isClosed_closedBall.isOpen_compl
    (fun y hy=>hzero y hy)
  have hzGlobal:∀ᵐy:E∂volume,y∉closedBall (0:E) R₀→
      nativeWeakConformalDensity univ gE (fun z:E=>u (a⁻¹ • z)) y=0:=
    (ae_restrict_iff' measurableSet_closedBall.compl).mp hzD
  calc
    _=∫y in closedBall (0:E) R₀,(F_E:E→ℝ) y*η (e y):=
      nativeDensityChartSourceCLM_pairing g gE e he hei (isCompact_closedBall (0:E) R₀) hKs hcoeff F_E η
    _=∫y in closedBall (0:E) R₀,nativeWeakConformalDensity univ gE (fun z:E=>u (a⁻¹ • z)) y*φ (a⁻¹ • y):=by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (s:=closedBall (0:E) R₀) hF,
        ae_restrict_mem measurableSet_closedBall] with y hy hyK
      exact congrArg₂ (·*·) hy (htest y hyK).symm
    _=∫y:E,nativeWeakConformalDensity univ gE (fun z:E=>u (a⁻¹ • z)) y*φ (a⁻¹ • y):=by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [hzGlobal] with y hy
      intro hyK
      rw [hy hyK,zero_mul]
    _=_:=nativeGlobalH2_physical_conformal_pairing gE ha hu φ

#print axioms nativeCompactH2_native_source_physical_pairing
end Yamabe3.Analysis.SpherePolar
