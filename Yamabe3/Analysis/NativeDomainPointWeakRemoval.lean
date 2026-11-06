import Yamabe3.Analysis.NativePointWeakRemoval

/-! Domain-preserving removal of one point. The actual smooth tests
keep their original compact support inside the domain throughout the
H1 approximation; no boundary condition or trace is changed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private def domainPointNativeH1Normed (g:RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] domainPointNativeH1Normed

theorem native_point_cutoff_test_support
    (g:RiemannianMetric 3 M) (q:M) (φ κ:EnergyTest g.leviCivitaData univ)
    (hκ:(κ:M→ℝ)=ᶠ[𝓝 q](fun _=>1)) :
    tsupport (φ-κ.mulSmooth φ φ.smooth:M→ℝ)⊆tsupport (φ:M→ℝ)∩{q}ᶜ := by
  intro x hx
  constructor
  · by_contra hn
    have hf:(φ:M→ℝ)=ᶠ[𝓝 x](fun _=>0):=notMem_tsupport_iff_eventuallyEq.mp hn
    have he:(φ-κ.mulSmooth φ φ.smooth:M→ℝ)=ᶠ[𝓝 x](fun _=>0):=by
      filter_upwards [hf] with y hy
      change φ y-φ y*κ y=0
      rw [hy,zero_mul,sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
  · change x≠q
    intro heq
    subst x
    have he:(φ-κ.mulSmooth φ φ.smooth:M→ℝ)=ᶠ[𝓝 q](fun _=>0):=by
      filter_upwards [hκ] with y hy
      change φ y-φ y*κ y=0
      rw [hy,mul_one,sub_self]
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx

theorem native_point_cutoff_test_tendsto
    (g:RiemannianMetric 3 M) (κ:ℕ→EnergyTest g.leviCivitaData univ)
    (hκ0:Tendsto (fun n=>(κ n:H1Zero g.leviCivitaData univ)) atTop (𝓝 0))
    (φ:EnergyTest g.leviCivitaData univ) :
    Tendsto (fun n=>((φ-(κ n).mulSmooth φ φ.smooth):H1Zero g.leviCivitaData univ)) atTop
      (𝓝 (φ:H1Zero g.leviCivitaData univ)) := by
  obtain ⟨C,hC,hbound⟩:=exists_mulSmooth_norm_bound (D:=g.leviCivitaData) (Ω:=univ)
    (φ:M→ℝ) φ.smooth φ.hasCompactSupport
  have hkn:Tendsto (fun n=>‖κ n‖) atTop (𝓝 0):=by
    simpa only [Completion.norm_coe] using tendsto_zero_iff_norm_tendsto_zero.mp hκ0
  have hmn:Tendsto (fun n=>‖(κ n).mulSmooth φ φ.smooth‖) atTop (𝓝 0):=
    squeeze_zero (fun n=>norm_nonneg _) (fun n=>hbound (κ n)) (by simpa only [mul_zero] using hkn.const_mul C)
  have hm:Tendsto (fun n=>((κ n).mulSmooth φ φ.smooth:H1Zero g.leviCivitaData univ)) atTop (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Completion.norm_coe] using hmn
  simpa only [Completion.coe_sub,sub_zero] using
    (tendsto_const_nhds (x:=(φ:H1Zero g.leviCivitaData univ))).sub hm

theorem native_point_tests_determine_in_domain
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {R:ℝ} (hR:0<R) (hRK:closedBall (0:E) R⊆K)
    (Ω:Set M) (L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ)
    (hL:∀φ:EnergyTest g.leviCivitaData univ,tsupport (φ:M→ℝ)⊆Ω∩{e 0}ᶜ →
      L (φ:H1Zero g.leviCivitaData univ)=0)
    (φ:EnergyTest g.leviCivitaData univ) (hs:tsupport (φ:M→ℝ)⊆Ω) :
    L (φ:H1Zero g.leviCivitaData univ)=0 := by
  obtain ⟨κ,hκ,hκ0⟩:=exists_nativePointEnergyCutoffSequence g e he hei hK hKs hR hRK
  apply (isClosed_eq L.continuous continuous_const).mem_of_tendsto (native_point_cutoff_test_tendsto g κ hκ0 φ)
  apply Eventually.of_forall
  intro n
  change L ((φ:H1Zero g.leviCivitaData univ)-((κ n).mulSmooth φ φ.smooth:H1Zero g.leviCivitaData univ))=0
  simpa only [Completion.coe_sub] using hL (φ-(κ n).mulSmooth φ φ.smooth) ((native_point_cutoff_test_support g (e 0) φ (κ n) (hκ n)).trans (inter_subset_inter_left _ hs))

variable [CompactSpace M] [ConnectedSpace M]

theorem nativeForcedEnergySpace_remove_point
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {R:ℝ} (hR:0<R) (hRK:closedBall (0:E) R⊆K)
    (Ω:Set M) (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (hlocal:(W,F)∈nativeForcedEnergySpace g B hB (Ω∩{e 0}ᶜ)) :
    (W,F)∈nativeForcedEnergySpace g B hB Ω := by
  let L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ:=
    closedYamabeJacobianForm g B hB W-(innerSL ℝ F).comp (toL2 g.leviCivitaData univ)
  intro φ hs
  exact sub_eq_zero.mp (native_point_tests_determine_in_domain g e he hei hK hKs hR hRK Ω L
    (fun ψ hψ=>sub_eq_zero.mpr (hlocal ψ hψ)) φ hs)

#print axioms native_point_cutoff_test_support
#print axioms native_point_cutoff_test_tendsto
#print axioms native_point_tests_determine_in_domain
#print axioms nativeForcedEnergySpace_remove_point
end Yamabe3.Analysis.SpherePolar
