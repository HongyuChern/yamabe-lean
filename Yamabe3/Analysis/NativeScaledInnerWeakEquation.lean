import Yamabe3.Analysis.NativeScaledSingularSource
import Yamabe3.Analysis.NativeH2DensitySourceEquation
import Yamabe3.Analysis.NativeForcedEnergyLocality
import Yamabe3.Analysis.NativeDomainPointWeakRemoval
import Yamabe3.Analysis.NativeForcedEnergyDataMembership

/-! Construct the actual native effective L2 source for the SAME
completed inner field and original source. Local H2 equations are
transported and glued, and the point is removed by actual H1 tests.
The singular potential product is retained explicitly in the source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic Delaunay GreenParametrix PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
local notation "Ounit" => (ball (0:E) 1\{(0:E)})

theorem nativeScaledInner_same_field_weak_equation
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0<R₀) (hKs:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    {κ:ℝ} (p:DelaunayPhaseData κ) {a:ℝ} (ha:0<a)
    (hfit:euclideanDilatedDomain a (ball (0:E) 1)⊆closedBall (0:E) R₀)
    (f:HalfEndSourceValue) (u:E→ℝ) (hum:Measurable u)
    (hpot:MemLp (fun x=>nativeHalfEndPotentialCoefficient p.potential x*u x) 2 (volume.restrict Ounit))
    (W:H1Zero g.leviCivitaData univ)
    (hrep:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict
      (e '' euclideanDilatedDomain a (ball (0:E) 1))]coordinateExtension e (fun x:E=>u (a⁻¹ • x)))
    (hlocal:∀U:Set E,IsOpen U →IsCompact (closure U) →closure U⊆Ounit →
      MemWkp 2 2 u U ∧ nativeWeakRescaledDelaunayJacobian U gE a p.orbit p.phase u
        =ᵐ[volume.restrict U]fun x=>halfEndEuclideanPhysicalSource f x/8):
    ∃F_E:Lp ℝ 2 (volume:Measure E),
      (F_E:E→ℝ)=ᵐ[volume](euclideanDilatedDomain a (ball (0:E) 1)).indicator
        (fun x=>gE.pullbackVolumeDensity id x*nativeScaledEffectiveSource gE a f p.potential u x) ∧
      (W,nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hKs F_E)∈
        nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const
          (e '' euclideanDilatedDomain a (ball (0:E) 1)):=by
  let K:=closedBall (0:E) R₀
  let Dfull:=euclideanDilatedDomain a (ball (0:E) 1)
  let Dpunct:=euclideanDilatedDomain a Ounit
  let Uphys:E→ℝ:=fun x=>u (a⁻¹ • x)
  let H:E→ℝ:=fun x=>gE.pullbackVolumeDensity id x*nativeScaledEffectiveSource gE a f p.potential u x
  have hDf:IsOpen Dfull:=isOpen_ball.preimage (continuous_const_smul a⁻¹)
  have hDp:IsOpen Dpunct:=(isOpen_ball.sdiff isClosed_singleton).preimage (continuous_const_smul a⁻¹)
  have hρtop:MemLp (fun x:E=>gE.pullbackVolumeDensity id x) ⊤ (volume.restrict K):=
    continuousOn_compact_memLp_top (isCompact_closedBall _ _) (native_density_smooth_positive gE).1.continuous.continuousOn
  have hHK:MemLp H 2 (volume.restrict K):=
    (nativeScaledEffectiveSource_memLp gE ha f p.potential hpot (isCompact_closedBall _ _)).mul' hρtop
  have hH:MemLp (Dfull.indicator H) 2 volume:=
    (memLp_indicator_iff_restrict hDf.measurableSet).mpr
      (hHK.mono_measure (Measure.restrict_mono hfit le_rfl))
  let F_E:=hH.toLp (Dfull.indicator H)
  have hFE:(F_E:E→ℝ)=ᵐ[volume]Dfull.indicator H:=hH.coeFn_toLp
  let F:=nativeDensityChartSourceCLM g gE e he hei (isCompact_closedBall (0:E) R₀) hKs F_E
  refine ⟨F_E,hFE,?_⟩
  have hP:(W,F)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const (e '' Dpunct):=by
    apply nativeForcedEnergySpace_of_local
    rintro y ⟨x,hx,rfl⟩
    have hxU:a⁻¹ • x∈Ounit:=hx
    obtain ⟨r,hr,hrO⟩:=Metric.isOpen_iff.mp (isOpen_ball.sdiff isClosed_singleton) _ hxU
    let U:=ball (a⁻¹ • x) (r/2)
    have hUc:IsCompact (closure U):=by
      dsimp only [U]
      rw [closure_ball _ (by positivity:r/2≠0)]
      exact isCompact_closedBall _ _
    have hUO:closure U⊆Ounit:=closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (by linarith:r/2<r)).trans hrO)
    let D:=euclideanDilatedDomain a U
    let d:E≃ₜE:=Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne')
    have hDc:closure D=d ⁻¹' closure U:=(d.preimage_closure U).symm
    have hDcK:closure D⊆K:=by
      rw [hDc]
      exact (preimage_mono (hUO.trans sdiff_subset)).trans hfit
    have hDcomp:IsCompact (closure D):=by rw [hDc];exact d.isCompact_preimage.mpr hUc
    have hD:IsOpen D:=isOpen_ball.preimage (continuous_const_smul a⁻¹)
    have hDs:D⊆e.source:=(subset_closure.trans hDcK).trans hKs
    have hDfull:D⊆Dfull:=preimage_mono ((subset_closure.trans hUO).trans sdiff_subset)
    have hΩ:IsOpen (e '' D):=e.isOpen_image_of_subset_source hD hDs
    refine ⟨e '' D,hΩ,⟨x,mem_ball_self (by positivity:r/2>0),rfl⟩,?_⟩
    obtain ⟨hu,hq⟩:=hlocal U isOpen_ball hUc hUO
    have h0:U⊆({0}ᶜ:Set E):=(subset_closure.trans hUO).trans (sdiff_subset_compl _ _)
    obtain ⟨huD,hqD⟩:=nativeWeak_physical_conformal_source gE p.orbit p.phase ha isOpen_ball h0 hu hq
    have hsource:nativeWeakConformalDensity D gE Uphys=ᵐ[volume.restrict D](F_E:E→ℝ):=by
      filter_upwards [hqD,ae_restrict_of_ae (s:=D) hFE,ae_restrict_mem hD.measurableSet] with z hz hf hzD
      have hzfull:z∈Dfull:=hDfull hzD
      have hn:‖z‖<a:=by
        have hn:=mem_ball_zero_iff.mp hzfull
        rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ha).le] at hn
        exact (inv_mul_lt_one₀ ha).mp hn
      have hz0:z≠0:=by
        intro hzero
        have hnot: a⁻¹ • z≠0:=(hUO (subset_closure hzD)).2
        exact hnot (by rw [hzero,smul_zero])
      rw [hf,indicator_of_mem hzfull]
      exact hz.trans (nativeScaledEffectiveSource_density_identity gE p ha f u
        ⟨mem_ball_zero_iff.mpr hn,hz0⟩).symm
    apply nativeH2_chart_density_source_equation g gE e he hei (isCompact_closedBall (0:E) R₀) hKs
      hcoeff hD hDcomp hDcK Uphys (hum.comp (continuous_const_smul a⁻¹).measurable) huD W F_E ?_ hsource
    have hr:(toL2 g.leviCivitaData univ W:M→ℝ)=ᵐ[g.volumeMeasure.restrict (e '' D)]coordinateExtension e Uphys:=
      ae_mono (Measure.restrict_mono (image_mono hDfull) le_rfl) hrep
    filter_upwards [hr,ae_restrict_mem hΩ.measurableSet] with z hz hzD
    obtain ⟨t,ht,rfl⟩:=hzD
    rw [hz,nativeCompactChartFunction,coordinateExtension_comp_apply e _ (hDs ht),
      coordinateExtension_comp_apply e _ (hDs ht),indicator_of_mem (subset_closure ht)]
  have hdomain:(e '' Dfull)∩{e 0}ᶜ=e '' Dpunct:=by
    ext y
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hne⟩
      refine ⟨x,⟨hx,?_⟩,rfl⟩
      intro hz
      have hx0:x=0:=(smul_eq_zero.mp hz).resolve_left (inv_ne_zero ha.ne')
      exact hne (by simp only [hx0,mem_singleton_iff])
    · rintro ⟨x,hx,rfl⟩
      refine ⟨⟨x,hx.1,rfl⟩,?_⟩
      intro heq
      have h0K:(0:E)∈K:=mem_closedBall_self hR₀.le
      have hx0:x=0:=e.injOn (hKs (hfit hx.1)) (hKs h0K) (by simpa only [mem_singleton_iff] using heq)
      exact hx.2 (by simpa only [hx0,smul_zero,mem_singleton_iff])
  apply nativeForcedEnergySpace_remove_point g (fun _:M=>0) contMDiff_const e he hei
    (isCompact_closedBall (0:E) R₀) hKs hR₀ (by exact subset_rfl)
    (e '' Dfull) W F
  simpa only [hdomain] using hP

#print axioms nativeScaledInner_same_field_weak_equation
end Yamabe3.Analysis.SpherePolar
