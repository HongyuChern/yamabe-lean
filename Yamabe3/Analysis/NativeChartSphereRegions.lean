import Yamabe3.Analysis.NativeForcedThreeRegionGluing
import Yamabe3.Analysis.NativeChartCollarTail
import Yamabe3.Analysis.NativeActualFeedbackCollarIdentity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
attribute [local instance] Classical.propDecidable
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet

theorem euclideanDilated_unit_ball {a:ℝ} (ha:0<a):
    euclideanDilatedDomain a (ball (0:E) 1)=ball (0:E) a:=by
  ext x
  change (a⁻¹ • x∈ball (0:E) 1)↔x∈ball (0:E) a
  rw [mem_ball_zero_iff,mem_ball_zero_iff,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le]
  exact inv_mul_lt_one₀ ha

variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeChartBall_boundary_eq_sphere
    (e:OpenPartialHomeomorph E M) (a:ℝ) (hs:closedBall (0:E) a⊆e.source):
    (e '' closedBall (0:E) a) \ (e '' ball (0:E) a)=e '' sphere (0:E) a:=by
  ext y
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hxI⟩
    refine ⟨x,?_,rfl⟩
    have hn:‖x‖≤a:=mem_closedBall_zero_iff.mp hx
    have hge:a≤‖x‖:=le_of_not_gt (fun h=>hxI ⟨x,mem_ball_zero_iff.mpr h,rfl⟩)
    simpa only [mem_sphere,dist_zero_right] using le_antisymm hn hge
  · rintro ⟨x,hx,rfl⟩
    have hxC:x∈closedBall (0:E) a:=sphere_subset_closedBall hx
    refine ⟨⟨x,hxC,rfl⟩,?_⟩
    rintro ⟨z,hz,hez⟩
    have hzx:z=x:=e.injOn (hs (ball_subset_closedBall hz)) (hs hxC) hez
    subst z
    have hn:‖x‖=a:=by simpa only [mem_sphere,dist_zero_right] using hx
    exact (not_lt_of_ge hn.ge) (mem_ball_zero_iff.mp hz)

theorem nativeChartBall_boundary_collar
    (e:OpenPartialHomeomorph E M) {a:ℝ} (ha:0<a)
    (hs:closedBall (0:E) a⊆e.source):
    (e '' closedBall (0:E) a) \ (e '' ball (0:E) a)⊆e '' euclideanDilatedDomain a nativePoissonEntranceCollar:=by
  rw [nativeChartBall_boundary_eq_sphere e a hs]
  rintro y ⟨x,hx,rfl⟩
  refine ⟨x,?_,rfl⟩
  have hn:‖x‖=a:=by simpa only [mem_sphere,dist_zero_right] using hx
  have hnu:‖a⁻¹ • x‖=1:=by
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le,hn,inv_mul_cancel₀ ha.ne']
  exact native_unit_sphere_mem_collar ⟨a⁻¹ • x,by simpa only [mem_sphere,dist_zero_right] using hnu⟩

theorem nativeChartSphere_actual_global_source
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a:ℝ} (ha:0<a) (hs:closedBall (0:E) a⊆e.source)
    (hCol:euclideanDilatedDomain a nativePoissonEntranceCollar⊆e.source)
    (W:H1Zero g.leviCivitaData univ) (Fi Fo:Lp ℝ 2 g.volumeMeasure)
    (hi:(W,Fi)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const
      (e '' euclideanDilatedDomain a (ball (0:E) 1)))
    (ho:(W,Fo)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' closedBall (0:E) a)ᶜ)
    (hLocal:∀x∈e '' euclideanDilatedDomain a nativePoissonEntranceCollar,
      ∃U:Set M,IsOpen U ∧ x∈U ∧ U⊆e '' euclideanDilatedDomain a nativePoissonEntranceCollar ∧
        ∃G:Lp ℝ 2 g.volumeMeasure,(W,G)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const U):
    ∃F:Lp ℝ 2 g.volumeMeasure,
      (F:M→ℝ)=ᵐ[g.volumeMeasure](e '' ball (0:E) a).piecewise (Fi:M→ℝ) (Fo:M→ℝ) ∧
      (W,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const univ:=by
  have hI:IsOpen (e '' ball (0:E) a):=e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hs)
  have hC:IsClosed (e '' closedBall (0:E) a):=
    ((isCompact_closedBall (0:E) a).image_of_continuousOn (e.continuousOn.mono hs)).isClosed
  have hColOpen:IsOpen (e '' euclideanDilatedDomain a nativePoissonEntranceCollar):=
    e.isOpen_image_of_subset_source ((nativePolarTimeWindow_open (1/2)).preimage (continuous_const_smul a⁻¹)) hCol
  have hNull:g.volumeMeasure ((e '' closedBall (0:E) a) \ (e '' ball (0:E) a))=0:=by
    rw [nativeChartBall_boundary_eq_sphere e a hs]
    exact EuclideanSphereTrace.native_chart_sphere_volume_zero g e he hei a (sphere_subset_closedBall.trans hs)
  rw [euclideanDilated_unit_ball ha] at hi
  exact nativeForcedEnergySpace_three_regions g (fun _:M=>0) contMDiff_const
    (e '' ball (0:E) a) (e '' closedBall (0:E) a) (e '' euclideanDilatedDomain a nativePoissonEntranceCollar)
    hI hC hColOpen (image_mono ball_subset_closedBall) (nativeChartBall_boundary_collar e ha hs) hNull W Fi Fo hi ho hLocal

#print axioms euclideanDilated_unit_ball
#print axioms nativeChartBall_boundary_eq_sphere
#print axioms nativeChartBall_boundary_collar
#print axioms nativeChartSphere_actual_global_source
end Yamabe3.Analysis.SpherePolar
