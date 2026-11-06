import Yamabe3.Analysis.NativeGlobalH2ChartSource
import Yamabe3.Analysis.NativeChartAeTransport

/-! The actual global H2 coordinate field supplies its native source
without an added measurable-representative hypothesis. The auxiliary
measurable representative is identified by volume a.e. transport and
weak derivative uniqueness, then eliminated from the source formula. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Manifold Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.Weak

 theorem nativeWeakConformalDensity_congr
    {O:Set E} (hO:IsOpen O) (g:RiemannianMetric 3 E) {u v:E→ℝ}
    (he:u=ᵐ[volume.restrict O]v):
    nativeWeakConformalDensity O g u=ᵐ[volume.restrict O]nativeWeakConformalDensity O g v:=by
  have hj:=nativeWeakRescaledDelaunayJacobian_congr hO g 1 (fun _=>0) 0 he
  filter_upwards [hj,he] with x hx he
  rw [nativeWeakJacobian_one_conformal_density O g (fun _=>0) 0 u x,
    nativeWeakJacobian_one_conformal_density O g (fun _=>0) 0 v x,hx,he]

variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

 theorem nativeGlobalH2_chart_canonical_density_source
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (R₀:ℝ) (hKs:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {O:Set E} (hO:IsOpen O) (hOK:O⊆closedBall (0:E) R₀)
    (u:E→ℝ) (hu:MemWkp 2 2 u univ)
    (W:H1Zero g.leviCivitaData univ)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' O)]coordinateExtension e u):
    ∃F_E:Lp ℝ 2 (volume:Measure E),
      (F_E:E→ℝ)=ᵐ[volume]((closedBall (0:E) R₀).indicator
        (nativeWeakConformalDensity (ball (0:E) (R₀+1)) gE u)) ∧
      (W,nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hKs F_E)∈
        nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' O):=by
  have hm:MemLp u 2 (volume:Measure E):=by simpa only [Measure.restrict_univ] using hu.memLp
  let v:E→ℝ:=hm.aestronglyMeasurable.mk u
  have hvMeas:Measurable v:=hm.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have huv:u=ᵐ[volume]v:=hm.aestronglyMeasurable.ae_eq_mk
  have hv:MemWkp 2 2 v univ:=
    (MemWkp_congr_ae (by norm_num) isOpen_univ (by simpa only [Measure.restrict_univ] using huv)).mp hu
  have hnat:=coordinateExtension_congr_volume_ae g e he hei huv
  obtain ⟨F_E,hF,hforced⟩:=nativeGlobalH2_chart_actual_density_source g gE e he hei R₀ hKs hcoeff hO hOK
    v hvMeas hv W (hrep.trans (ae_restrict_of_ae (s:=e '' O) hnat))
  have hKB:closedBall (0:E) R₀⊆ball (0:E) (R₀+1):=by
    intro x hx
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) (by linarith))
  have hd:=nativeWeakConformalDensity_congr isOpen_ball gE (ae_restrict_of_ae (s:=ball (0:E) (R₀+1)) huv)
  have hdK:=ae_mono (Measure.restrict_mono hKB le_rfl) hd
  have hh:=(ae_restrict_iff' measurableSet_closedBall).mp hdK
  have hraw:(closedBall (0:E) R₀).indicator (nativeWeakConformalDensity (ball (0:E) (R₀+1)) gE v)=ᵐ[volume]
      (closedBall (0:E) R₀).indicator (nativeWeakConformalDensity (ball (0:E) (R₀+1)) gE u):=by
    filter_upwards [hh] with x hx
    by_cases hxK:x∈closedBall (0:E) R₀
    · rw [indicator_of_mem hxK,indicator_of_mem hxK]
      exact (hx hxK).symm
    · rw [indicator_of_notMem hxK,indicator_of_notMem hxK]
  exact ⟨F_E,hF.trans hraw,hforced⟩

#print axioms nativeWeakConformalDensity_congr
#print axioms nativeGlobalH2_chart_canonical_density_source
end Yamabe3.Analysis.SpherePolar
