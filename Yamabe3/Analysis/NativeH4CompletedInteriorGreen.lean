import Yamabe3.Analysis.NativeC1ChartEnergy
import Yamabe3.Analysis.NativeScaledH4Integrability
import Yamabe3.Analysis.NativeC1OffZeroSphereGreen
import Yamabe3.Analysis.NativeH4InteriorEnergyData

/-! The same actual interior H1 element has the genuine induced-area
Green flux of its retained, physically scaled H4 field. The compact test
extension preserves the whole ball and may have nonzero sphere values. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology Manifold ContDiff Bundle
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
namespace Yamabe3.Analysis
open SpherePolar EuclideanSphereTrace UniformElliptic NativeChartSphereMetric
open PoincareMT.LeviCivitaData.Dirichlet GreenMass.NativeGaussSphereArea
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "S" => SpherePolar.S
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

private theorem gradient_germ (g:RiemannianMetric 3 E) {f h:E→ℝ} {x:E} (he:f=ᶠ[𝓝 x]h) :
    g.leviCivitaData.gradient f x=g.leviCivitaData.gradient h x := by
  unfold LeviCivitaData.gradient
  rw [Poincare.mvfderiv_eq_of_eventuallyEq he]

theorem nativeH4_completed_interior_green
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss:∀x v:E,gE.inner x x v=inner ℝ x v)
    {a:ℝ} (ha:0<a) (hs:closedBall (0:E) (3*a)⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) (2*a),gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hSphere:∀θ:S,GreenMass.SphereMeasure.dilation a θ∈e.source)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    {L:E→ℝ} (hL:ContDiff ℝ 1 L) (hLc:HasCompactSupport L) (hLs:tsupport L⊆e.source)
    (hnear:∀x∈closedBall (0:E) (2*a),L=ᶠ[𝓝 x](fun y=>u.val (a⁻¹ • y)))
    (ell:H1Zero g.leviCivitaData univ)
    (hrep:(toL2 g.leviCivitaData univ ell:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension e L)
    (φ:EnergyTest g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g (e '' closedBall (0:E) a) ell (φ:H1Zero g.leviCivitaData univ)+
      (∫x in closedBall (0:E) a,φ (e x)*gE.leviCivitaData.laplacian (nativeScaledOffZero ha u).val x ∂gE.volumeMeasure)=
      ∫θ:S,φ (e (a • (θ:E)))*fderiv ℝ (nativeScaledOffZero ha u).val (a • (θ:E)) (θ:E)
        ∂(chartRadiusMetric g e he hei a ha.ne' hSphere).volumeMeasure := by
  let U:=nativeScaledOffZero ha u
  have h2:closedBall (0:E) (2*a)⊆e.source:=(closedBall_subset_closedBall (by linarith)).trans hs
  have h12:closedBall (0:E) a⊆closedBall (0:E) (2*a):=closedBall_subset_closedBall (by linarith)
  have h13:closedBall (0:E) a⊆ball (0:E) (3*a):=closedBall_subset_ball (by linarith)
  have hUC:ContDiff ℝ 1 U.val:=nativeScaledH4_C1 ha v u h0 hu
  have hUL:=nativeScaledH4_density_laplacian_locallyIntegrable gE ha v u h0 hu
  obtain ⟨Ψ,hΨ,hΨc,_,hΨnear⟩:=exists_compact_C2_supported_extension e.open_source
    (isCompact_closedBall (0:E) (2*a)) h2
    ((φ.smooth.comp_contMDiffOn he).contDiffOn.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have htest (x:E) (hx:x∈closedBall (0:E) a):Ψ x=φ (e x):=(hΨnear x (h12 hx)).self_of_nhds
  have hfield(x:E)(hx:x∈closedBall (0:E) a):((coordinateExtension e L)∘e)=ᶠ[𝓝 x] U.val:=by
    apply EventuallyEq.trans _ (hnear x (h12 hx))
    filter_upwards [e.open_source.mem_nhds (h2 (h12 hx))] with y hy
    exact coordinateExtension_comp_apply e L hy
  have henergy:=nativeRestrictedGradientEnergy_C1_chart g gE e he hei
    (isCompact_closedBall (0:E) (3*a)) hs ball_subset_closedBall isOpen_ball
    (isCompact_closedBall (0:E) a) h13 (fun x hx=>hcoeff x (h12 hx)) ell
    (contMDiff_coordinateExtension_C1 e hei hL hLc hLs) hrep φ
  have heq:nativeRestrictedGradientEnergy g (e '' closedBall (0:E) a) ell (φ:H1Zero g.leviCivitaData univ)=
      ∫x in closedBall (0:E) a,gE.inner x (gE.leviCivitaData.gradient Ψ x) (gE.leviCivitaData.gradient U.val x) ∂gE.volumeMeasure := by
    rw [henergy]
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    dsimp only
    rw [gradient_germ gE (hfield x hx),←gradient_germ gE (hΨnear x (h12 hx)),gE.symm]
  have hi:Integrable (fun x=>Ψ x*gE.leviCivitaData.laplacian U.val x) gE.volumeMeasure:=
    nativeC1OffZero_mul_laplacian_integrable gE U hUL hΨ.continuous hΨc
  have hg:Integrable (fun x=>gE.inner x (gE.leviCivitaData.gradient Ψ x) (gE.leviCivitaData.gradient U.val x)) gE.volumeMeasure:=
    NativeC1Green.integrable_inner_gradient_C1 gE.leviCivitaData (hΨ.of_le (by norm_num)).contMDiff hUC.contMDiff hΨc
  have hgreen:=nativeC1OffZero_closedBall_sphere_green gE hGauss U hUC hUL ha hΨ hΨc
  rw [integral_add hi.integrableOn hg.integrableOn,←heq] at hgreen
  have hvol:(∫x in closedBall (0:E) a,Ψ x*gE.leviCivitaData.laplacian U.val x ∂gE.volumeMeasure)=
      ∫x in closedBall (0:E) a,φ (e x)*gE.leviCivitaData.laplacian U.val x ∂gE.volumeMeasure :=
    setIntegral_congr_fun measurableSet_closedBall (fun x hx=>by rw [htest x hx])
  have hsphere (θ:S):a • (θ:E)∈closedBall (0:E) a:=by
    rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]
  have hm:=chartRadiusMetric_eq_gaussRadiusMetric g gE e he hei a ha.ne' hSphere
    (fun θ=>hcoeff _ (h12 (hsphere θ)))
  rw [hvol] at hgreen
  rw [hm]
  have hb:(∫θ:S,Ψ (a • (θ:E))*fderiv ℝ U.val (a • (θ:E)) (θ:E) ∂(gaussRadiusMetric gE a ha.ne').volumeMeasure)=
      ∫θ:S,φ (e (a • (θ:E)))*fderiv ℝ U.val (a • (θ:E)) (θ:E) ∂(gaussRadiusMetric gE a ha.ne').volumeMeasure:=by
    apply integral_congr_ae
    exact Eventually.of_forall fun θ=>by dsimp only; rw [htest _ (hsphere θ)]
  rw [hb] at hgreen
  linarith only [hgreen]

theorem nativeBoundarySphereSource
    (g:RiemannianMetric 3 M) {q:M} (G:NativeBoundaryGeometry g q) (θ:S) :
    GreenMass.SphereMeasure.dilation G.a θ∈G.e.source := by
  apply G.hs
  change G.a • (θ:E)∈closedBall (0:E) (2*G.a)
  rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ G.ha.le]
  linarith only [G.ha]

theorem exists_native_H4_completed_interior_green
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g) {q:M}
    (G:NativeBoundaryGeometry g q) (h3:closedBall (0:E) (3*G.a)⊆G.e.source)
    (b:M→ℝ) (hb:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (hsmall:60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    (F:Lp ℝ 2 g.volumeMeasure) :
    ∃(L:E→ℝ) (ell:H1Zero g.leviCivitaData univ)
      (d:NativeWeakEllipticDataSpace g G.exterior (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb)),
      (toL2 g.leviCivitaData univ ell:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension G.e L ∧
      (∀x∈closedBall (0:E) (2*G.a),coordinateExtension G.e L (G.e x)=u.val (G.a⁻¹ • x)) ∧
      d.val.2=F ∧ G.trace d.val.1=G.trace ell ∧
      ∀φ:EnergyTest g.leviCivitaData univ,
        nativeRestrictedGradientEnergy g (G.e '' closedBall (0:E) G.a) ell (φ:H1Zero g.leviCivitaData univ)+
          (∫x in closedBall (0:E) G.a,φ (G.e x)*G.gE.leviCivitaData.laplacian (nativeScaledOffZero G.ha u).val x ∂G.gE.volumeMeasure)=
          ∫θ:S,φ (G.e (G.a • (θ:E)))*fderiv ℝ (nativeScaledOffZero G.ha u).val (G.a • (θ:E)) (θ:E)
            ∂(chartRadiusMetric g G.e G.he G.hei G.a G.ha.ne' (nativeBoundarySphereSource g G)).volumeMeasure := by
  obtain ⟨L,ell,d,_,_,hL,hLc,hLs,hnear,hrep,hpoint,hF,hT,_,_⟩:=
    exists_native_H4_interior_exterior_data g hY G h3 b hb hsmall v u h0 hu F
  refine ⟨L,ell,d,hrep,hpoint,hF,hT,?_⟩
  intro φ
  exact nativeH4_completed_interior_green g G.gE G.e G.he G.hei G.hGauss G.ha h3 G.hcoeff
    (nativeBoundarySphereSource g G) v u h0 hu hL hLc (hLs.trans (ball_subset_closedBall.trans h3)) hnear ell hrep φ

#print axioms nativeH4_completed_interior_green
#print axioms exists_native_H4_completed_interior_green
end Yamabe3.Analysis
