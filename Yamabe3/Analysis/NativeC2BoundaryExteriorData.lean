import Yamabe3.Analysis.NativeC2BoundaryCutoff
import Yamabe3.Analysis.NativeC1ExteriorData
import Yamabe3.Analysis.NativeGeometricDirichletAssembly
import Yamabe3.Analysis.NativeLinearChartData

/-! At a prescribed small radius the original metric supplies the same
normal-chart boundary geometry. The actual C2 field supplies its H1 lifting;
the native exterior solver supplies Data for every specified L2 source.
The conormal functional is retained as an actual output, not identified
with the interior one without the remaining feedback argument. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff Manifold ENNReal
namespace Yamabe3.Analysis
open SpherePolar NativeChartSphereMetric PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem exists_native_linear_chart_boundary_geometry
    (g:RiemannianMetric 3 M) (q:M) {r:ℝ} (hr:0<r) (h3:3*r ≤ (nativeLinearChart g q).radius) :
    ∃G:NativeBoundaryGeometry g q,G.e=(nativeLinearChart g q).chart ∧
      G.gE=(nativeLinearChart g q).metric ∧ G.a=r ∧ closedBall (0:E) (3*G.a)⊆G.e.source := by
  let χ:=nativeLinearChart g q
  have hrad:Continuous (fun θ:S=>r • (θ:E)):=by fun_prop
  have hρc:Continuous (fun θ:S=>χ.metric.pullbackVolumeDensity id (r • (θ:E))):=
    (GreenParametrix.native_density_smooth_positive χ.metric).1.continuous.comp hrad
  obtain ⟨C,hC⟩:=isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have h2:2*r ≤ χ.radius := (by linarith : 2*r ≤ 3*r).trans h3
  let G:NativeBoundaryGeometry g q:={
    e:=χ.chart
    gE:=χ.metric
    a:=r
    C:=max C 0
    ha:=hr
    he:=χ.smooth
    hei:=χ.inverse_smooth
    hs:=(closedBall_subset_closedBall h2).trans χ.source
    center:=χ.center
    hGauss:=χ.gauss
    hcoeff:=fun x hx=>χ.coefficients x (closedBall_subset_closedBall h2 hx)
    hC:=le_max_right C 0
    hρ:=fun θ=>(le_abs_self _).trans ((show |χ.metric.pullbackVolumeDensity id (r • (θ:E))| ≤ C from by
      simpa only [Real.norm_eq_abs] using hC θ (mem_univ θ)).trans (le_max_left _ _)) }
  exact ⟨G,rfl,rfl,rfl,(closedBall_subset_closedBall h3).trans χ.source⟩

theorem exists_native_C2_boundary_exterior_data
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) {q:M}
    (G:NativeBoundaryGeometry g q) (h3:closedBall (0:E) (3*G.a)⊆G.e.source)
    (b:M→ℝ) (hb:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (hsmall:60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g)
    {u:E→ℝ} (hu:ContDiffOn ℝ 2 u ({0}ᶜ:Set E)) (F:Lp ℝ 2 g.volumeMeasure) :
    ∃(L:E→ℝ) (ell:H1Zero g.leviCivitaData univ)
      (d:NativeWeakEllipticDataSpace g G.exterior (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb)),
      ContDiff ℝ 2 L ∧ HasCompactSupport L ∧
      tsupport L⊆ball (0:E) (3*G.a)\closedBall (0:E) (G.a/3) ∧
      (∀θ:S,L=ᶠ[𝓝 (G.a • (θ:E))] (fun y:E=>u (G.a⁻¹ • y))) ∧
      (toL2 g.leviCivitaData univ ell:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension G.e L ∧
      d.val.2=F ∧ G.trace d.val.1=G.trace ell ∧
      (G.trace d.val.1:S→ℝ)=ᵐ[(chartRadiusMetric g G.e G.he G.hei G.a G.ha.ne'
        (fun θ=>G.hs (by change G.a • (θ:E)∈closedBall (0:E) (2*G.a); rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ G.ha.le]; linarith only [G.ha]))).volumeMeasure]
        (fun θ:S=>u (θ:E)) ∧
      ∀v:H1Zero g.leviCivitaData univ,
        nativeRestrictedEllipticForm g G.exterior (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) d.val.1 v-
          (∫x in G.exterior,F x*toL2 g.leviCivitaData univ v x ∂g.volumeMeasure)=
          EuclideanSphereTrace.nativeWeakPhysicalConormalCLM g G.gE G.e G.he G.hei G.hGauss G.ha G.hs G.hcoeff G.hC G.hρ
            (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) d
            (HilbertTraceQuotient.quotientMap G.trace v) := by
  obtain ⟨L,hL,hLc,hLs,hnear⟩:=exists_scaled_C2_boundary_cutoff G.ha hu
  let O:=ball (0:E) (3*G.a)\closedBall (0:E) (G.a/3)
  have hO:IsOpen O:=isOpen_ball.sdiff isClosed_closedBall
  have hOK:O⊆closedBall (0:E) (3*G.a):=fun x hx=>ball_subset_closedBall hx.1
  have hAnn:sphereTraceAnnulus G.a (2*G.a)⊆O := by
    intro x hx
    constructor
    · rw [mem_ball,dist_zero_right]; exact hx.2.trans_lt (by linarith only [G.ha])
    · rw [mem_closedBall,dist_zero_right]; linarith only [hx.1,G.ha]
  obtain ⟨ell,d,hrep,hF,hT,htr,hcon⟩:=exists_native_C1_forced_exterior_data g hY b hb hsmall
    G.gE G.e G.he G.hei G.hGauss G.ha G.hs G.hcoeff G.hC G.hρ
    hO (isCompact_closedBall _ _) h3 hOK (hL.of_le (by norm_num)) hLc hLs hAnn F
  refine ⟨L,ell,d,hL,hLc,hLs,hnear,hrep,hF,hT,?_,hcon⟩
  filter_upwards [htr] with θ hθ
  exact hθ.trans (by
    rw [(hnear θ).self_of_nhds]
    simp only [smul_smul,inv_mul_cancel₀ G.ha.ne',one_smul])

#print axioms exists_native_linear_chart_boundary_geometry
#print axioms exists_native_C2_boundary_exterior_data
end Yamabe3.Analysis
