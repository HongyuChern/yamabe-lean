import Yamabe3.Analysis.NativeH4GraphC1Removal
import Yamabe3.Analysis.NativeC2BoundaryExteriorData
import Yamabe3.Analysis.NativeWeakPhysicalH1Gluing

/-! Actual H1 interior realization of the same retained H4 field, and
actual exterior Data for a prescribed source. Their physical values match
and produce one global H1 field. The exact remaining conormal residual is
retained; its cancellation is not inferred from value matching. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff Manifold ENNReal
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis
open SpherePolar NativeChartSphereMetric PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem exists_scaled_C1_interior_cutoff {r:ℝ} (hr:0<r)
    {u:E→ℝ} (hu:ContDiff ℝ 1 u) :
    ∃L:E→ℝ,ContDiff ℝ 1 L ∧ HasCompactSupport L ∧ tsupport L⊆ball (0:E) (3*r) ∧
      ∀x∈closedBall (0:E) (2*r),L=ᶠ[𝓝 x] (fun y:E=>u (r⁻¹ • y)) := by
  have hKO:closedBall (0:E) (2*r)⊆ball (0:E) (3*r):=closedBall_subset_ball (by linarith)
  obtain ⟨χ,hχ,hχc,hχO,_,hχone⟩:=PoincareMT.exists_contMDiff_cutoff_of_isCompact
    (n:=3) (isCompact_closedBall (0:E) (2*r)) isOpen_ball hKO
  have hd:ContDiff ℝ 1 χ:=hχ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  refine ⟨fun x=>χ x*u (r⁻¹ • x),hd.mul (hu.comp (contDiff_id.const_smul _)),
    hχc.mul_right,tsupport_mul_subset_left.trans hχO,?_⟩
  intro x hx
  filter_upwards [hχone x hx] with y hy
  simpa only [Pi.one_apply,one_mul] using congrArg (fun a:ℝ=>a*u (r⁻¹ • y)) hy

theorem exists_native_H4_interior_exterior_data
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g) {q:M}
    (G:NativeBoundaryGeometry g q) (h3:closedBall (0:E) (3*G.a)⊆G.e.source)
    (b:M→ℝ) (hb:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (hsmall:60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    (F:Lp ℝ 2 g.volumeMeasure) :
    ∃(L:E→ℝ) (ell:H1Zero g.leviCivitaData univ)
      (d:NativeWeakEllipticDataSpace g G.exterior (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb)),
      ContDiff ℝ 1 u.val ∧ HasFDerivAt u.val (0:E→L[ℝ]ℝ) 0 ∧
      ContDiff ℝ 1 L ∧ HasCompactSupport L ∧ tsupport L⊆ball (0:E) (3*G.a) ∧
      (∀x∈closedBall (0:E) (2*G.a),L=ᶠ[𝓝 x] (fun y:E=>u.val (G.a⁻¹ • y))) ∧
      (toL2 g.leviCivitaData univ ell:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension G.e L ∧
      (∀x∈closedBall (0:E) (2*G.a),coordinateExtension G.e L (G.e x)=u.val (G.a⁻¹ • x)) ∧
      d.val.2=F ∧ G.trace d.val.1=G.trace ell ∧
      (G.trace d.val.1:S→ℝ)=ᵐ[(chartRadiusMetric g G.e G.he G.hei G.a G.ha.ne'
        (fun θ=>G.hs (by change G.a • (θ:E)∈closedBall (0:E) (2*G.a); rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ G.ha.le]; linarith only [G.ha]))).volumeMeasure]
        (fun θ:S=>u.val (θ:E)) ∧
      ∀η:H1Zero g.leviCivitaData univ,
        nativeRestrictedEllipticForm g G.exterior (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) d.val.1 η-
          (∫x in G.exterior,F x*toL2 g.leviCivitaData univ η x ∂g.volumeMeasure)=
          EuclideanSphereTrace.nativeWeakPhysicalConormalCLM g G.gE G.e G.he G.hei G.hGauss G.ha G.hs G.hcoeff G.hC G.hρ
            (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) d
            (HilbertTraceQuotient.quotientMap G.trace η) := by
  have hC1:=nativeH4Graph_representative_C1 v u h0 hu
  obtain ⟨L,hL,hLc,hLs,hnear⟩:=exists_scaled_C1_interior_cutoff G.ha hC1.1
  have hAnn:sphereTraceAnnulus G.a (2*G.a)⊆ball (0:E) (3*G.a) := by
    intro x hx
    rw [mem_ball,dist_zero_right]
    exact hx.2.trans_lt (by linarith only [G.ha])
  obtain ⟨ell,d,hrep,hF,hT,htr,hcon⟩:=exists_native_C1_forced_exterior_data g hY b hb hsmall
    G.gE G.e G.he G.hei G.hGauss G.ha G.hs G.hcoeff G.hC G.hρ
    isOpen_ball (isCompact_closedBall _ _) h3 ball_subset_closedBall hL hLc hLs hAnn F
  refine ⟨L,ell,d,hC1.1,hC1.2,hL,hLc,hLs,hnear,hrep,?_,hF,hT,?_,hcon⟩
  · intro x hx
    rw [coordinateExtension_comp_apply G.e L (G.hs hx)]
    exact (hnear x hx).self_of_nhds
  · filter_upwards [htr] with θ hθ
    exact hθ.trans (by
      rw [(hnear _ (by rw [mem_closedBall,dist_zero_right,EuclideanSphereTrace.norm_sphereTrace_radial _ G.ha.le]; linarith only [G.ha])).self_of_nhds]
      simp only [smul_smul,inv_mul_cancel₀ G.ha.ne',one_smul])

theorem exists_native_H4_interior_exterior_energy_gluing
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g) {q:M}
    (G:NativeBoundaryGeometry g q) (h3:closedBall (0:E) (3*G.a)⊆G.e.source)
    (b:M→ℝ) (hb:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (hsmall:60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g)
    (v:HalfEndPhysicalH4Graph) (u:nativeC2OffZero) (h0:u.val 0=0)
    (hu:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) u.val (closedBall (0:E) 4))
    (F:Lp ℝ 2 g.volumeMeasure) :
    ∃(L:E→ℝ) (ell W:H1Zero g.leviCivitaData univ)
      (d:NativeWeakEllipticDataSpace g G.exterior (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb)),
      (toL2 g.leviCivitaData univ ell:M→ℝ)=ᵐ[g.volumeMeasure] coordinateExtension G.e L ∧
      (∀x∈closedBall (0:E) (2*G.a),coordinateExtension G.e L (G.e x)=u.val (G.a⁻¹ • x)) ∧
      d.val.2=F ∧ G.trace d.val.1=G.trace ell ∧
      (toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure]
        G.exterior.piecewise (toL2 g.leviCivitaData univ d.val.1) (coordinateExtension G.e L) ∧
      ∀η:H1Zero g.leviCivitaData univ,
        schrodingerForm g.leviCivitaData univ (by simpa using isCompact_univ) 8
          (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) W η-
          (∫x,F x*toL2 g.leviCivitaData univ η x ∂g.volumeMeasure)=
          EuclideanSphereTrace.nativeWeakPhysicalConormalCLM g G.gE G.e G.he G.hei G.hGauss G.ha G.hs G.hcoeff G.hC G.hρ
            (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) d
            (HilbertTraceQuotient.quotientMap G.trace η)+
          nativeWeakEnergySourceDataCLM g G.exteriorᶜ (nativeJacobianPotential g b)
            (nativeJacobianPotential_smooth g hb) (ell,F) η := by
  classical
  obtain ⟨L,ell,d,_,_,_,_,_,_,hrep,hpoint,hF,hT,_,hcon⟩:=
    exists_native_H4_interior_exterior_data g hY G h3 b hb hsmall v u h0 hu F
  obtain ⟨W,hW,hres,_⟩:=exists_native_physical_gluing_residual g G.gE G.e G.he G.hei G.hGauss G.ha G.hs
    G.hcoeff G.hC G.hρ (nativeJacobianPotential g b) (nativeJacobianPotential_smooth g hb) ell d.val.1 hT F
  refine ⟨L,ell,W,d,hrep,hpoint,hF,hT,?_,?_⟩
  · filter_upwards [hW,hrep] with x hx hy
    rw [hx]
    by_cases hm:x∈(G.e '' closedBall (0:E) G.a)ᶜ
    · simp only [NativeBoundaryGeometry.exterior,piecewise,hm,ite_true]
    · simp only [NativeBoundaryGeometry.exterior,piecewise,hm,ite_false,hy]
  · intro η
    rw [hres η,nativeWeakEnergySourceDataCLM_apply,nativeRestrictedL2SourceOperator_apply]
    exact congrArg (fun t:ℝ=>t+nativeWeakEnergySourceDataCLM g G.exteriorᶜ (nativeJacobianPotential g b)
      (nativeJacobianPotential_smooth g hb) (ell,F) η) (hcon η)

#print axioms exists_scaled_C1_interior_cutoff
#print axioms exists_native_H4_interior_exterior_data
#print axioms exists_native_H4_interior_exterior_energy_gluing
end Yamabe3.Analysis
