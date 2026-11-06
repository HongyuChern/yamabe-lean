import Yamabe3.Analysis.NativeC1ChartEnergyTrace
import Yamabe3.Analysis.NativeForcedDirichletDataAssembly

/-! A C1 coordinate field supplies the actual H1 lifting used by the
native exterior source solver. The exterior Data, source, literal value
trace and conormal functional belong to this one construction. Conormal
matching with an independently produced interior field is not asserted. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff Manifold ENNReal
namespace Yamabe3.Analysis
open SpherePolar NativeChartSphereMetric PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
variable (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g)
  (b:M→ℝ) (hb:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
  (hsmall:60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g)
  (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
  (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  (hGauss:∀x v:E,gE.inner x x v=inner ℝ x v)
  {a C:ℝ} (ha:0<a) (hsphere:closedBall (0:E) (2*a)⊆e.source)
  (hcoeff:∀x∈closedBall (0:E) (2*a),gE.euclideanCoefficients x=g.pullbackCoefficients e x)
  (hC:0 ≤ C) (hρ:∀θ:S,gE.pullbackVolumeDensity id (a • (θ:E)) ≤ C)

include hsphere in
private theorem C1Exterior_annulus_source : sphereTraceAnnulus a (2*a)⊆e.source := by
  intro x hx
  exact hsphere (by simpa only [mem_closedBall,dist_zero_right] using hx.2)
local notation "T" => nativePhysicalSphereTraceCLM g gE e he hei ha
  (show a<2*a from by linarith only [ha]) (show a∈Icc a (2*a) from ⟨le_rfl,by linarith only [ha]⟩)
  (C1Exterior_annulus_source e hsphere) hC
  (fun θ=>hcoeff _ (by change a • (θ:E)∈closedBall (0:E) (2*a); rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]; linarith only [ha]))
  (fun θ=>hGauss (a • (θ:E))) hρ
local notation "Oext" => (e '' closedBall (0:E) a)ᶜ
local notation "μ" => (chartRadiusMetric g e he hei a ha.ne'
  (fun θ=>hsphere (by change a • (θ:E)∈closedBall (0:E) (2*a); rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]; linarith only [ha]))).volumeMeasure

include hY hsmall in
theorem exists_native_C1_forced_exterior_data
    {O K:Set E} (hO:IsOpen O) (hK:IsCompact K) (hKs:K⊆e.source) (hOK:O⊆K)
    {u:E→ℝ} (hu:ContDiff ℝ 1 u) (hc:HasCompactSupport u) (hs:tsupport u⊆O)
    (hAnn:sphereTraceAnnulus a (2*a)⊆O) (F:Lp ℝ 2 g.volumeMeasure) :
    ∃(ell:H1Zero g.leviCivitaData univ)
      (d:NativeWeakEllipticDataSpace g Oext (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb)),
      (toL2 g.leviCivitaData univ ell:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension e u ∧
      d.val.2=F ∧ T d.val.1=T ell ∧
      (T d.val.1:S→ℝ)=ᵐ[μ] (fun θ:S=>u (a • (θ:E))) ∧
      ∀v:H1Zero g.leviCivitaData univ,
        nativeRestrictedEllipticForm g Oext (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) d.val.1 v-
          (∫x in Oext,F x*toL2 g.leviCivitaData univ v x ∂g.volumeMeasure)=
          EuclideanSphereTrace.nativeWeakPhysicalConormalCLM g gE e he hei hGauss ha hsphere hcoeff hC hρ
            (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) d
            (HilbertTraceQuotient.quotientMap T v) := by
  obtain ⟨ell,hrep,htr⟩:=exists_native_C1_chart_energy_with_trace g e he hei hO hK hKs hOK hu hc hs
    ha (show a<2*a by linarith only [ha]) (show a∈Icc a (2*a) from ⟨le_rfl,by linarith only [ha]⟩) hAnn
  obtain ⟨d,hF,hT,hcon⟩:=exists_native_forced_exterior_data_with_conormal g hY b hb hsmall
    gE e he hei hGauss ha hsphere hcoeff hC hρ ell F
  refine ⟨ell,d,hrep,hF,hT,?_,hcon⟩
  rw [hT]
  have hμ:=chartRadiusMetric_volume_le_nativeAngular g gE e he hei ha.ne' hC
    (fun θ=>hsphere (by change a • (θ:E)∈closedBall (0:E) (2*a); rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]; linarith only [ha]))
    (fun θ=>hcoeff _ (by change a • (θ:E)∈closedBall (0:E) (2*a); rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]; linarith only [ha]))
    (fun θ=>hGauss (a • (θ:E))) hρ
  exact (nativePhysicalSphereTraceCLM_ae_angularTrace g gE e he hei ha
    (show a<2*a by linarith only [ha]) (show a∈Icc a (2*a) from ⟨le_rfl,by linarith only [ha]⟩)
    (C1Exterior_annulus_source e hsphere) hC
    (fun θ=>hcoeff _ (by change a • (θ:E)∈closedBall (0:E) (2*a); rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]; linarith only [ha]))
    (fun θ=>hGauss (a • (θ:E))) hρ ell).trans
      ((Measure.absolutelyContinuous_of_le_smul hμ).ae_eq htr)

#print axioms exists_native_C1_forced_exterior_data
end Yamabe3.Analysis
