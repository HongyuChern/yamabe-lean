import Yamabe3.Analysis.NativeIncomingPotentialSource
import Yamabe3.Analysis.PhysicalOuterWindowReconstruction

/-! The SAME native potential source has an actual full angular time
source, fixed finite time support, uniform a^(-1/2) bound and exact whole
physical test pairing. Window coverage is proved using its true support. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic Delaunay
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def incomingWindowH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] incomingWindowH1Normed

theorem nativeIncomingPotentialCoefficient_zero_outside_window
    (gE:RiemannianMetric 3 E) (a τ c:ℝ) {χ:E→ℝ}
    (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1)) (m:ℕ) (hm:c < (m:ℝ)/2)
    {x:E} (hx:x∉nativePolarTimeWindow (Ioc (-(m:ℝ)/2) 0)) :
    nativeIncomingPotentialCoefficient gE a τ c χ x=0 := by
  by_cases hi:‖x‖ ≤ 2
  · exact nativeIncomingPotentialCoefficient_zero_inner gE a τ c h1 hi
  · have hn:0 < ‖x‖ := by linarith [lt_of_not_ge hi]
    have hx0:x≠0 := norm_pos_iff.mp hn
    have ht:0 ≤ Real.log ‖x‖ := Real.log_nonneg (by linarith [lt_of_not_ge hi])
    have hm':Real.log ‖x‖ ≥ (m:ℝ)/2 := by
      by_contra h
      have ht':-(m:ℝ)/2 < -Real.log ‖x‖ := by linarith [lt_of_not_ge h]
      exact hx ⟨hx0,ht',by linarith⟩
    apply nativeIncomingPotentialCoefficient_zero_outer
    have hh:Real.exp c < Real.exp (Real.log ‖x‖) := Real.exp_lt_exp.mpr (hm.trans_le hm')
    simpa only [Real.exp_log hn] using hh

theorem physicalL2OuterWindowSource_whole_physical_test (O:Set E) (hO:MeasurableSet O) (m:ℕ)
    (U:Lp ℝ 2 (volume.restrict O))
    (hzero:∀ᵐx:E∂volume.restrict O,x∉nativePolarTimeWindow (Ioc (-(m:ℝ)/2) 0) → U x=0)
    (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ) :
    inner ℝ (physicalL2OuterWindowSourceCLM O hO m U) (nativePhysicalPairTestL2 φ hφ hc h0)=
      ∫x in O,U x*φ x := by
  rw [physicalL2OuterWindowSource_physical_test O hO m U φ hφ hc h0]
  let W:=nativePolarTimeWindow (Ioc (-(m:ℝ)/2) 0)
  have hW:MeasurableSet W := nativePolarTimeWindow_measurable measurableSet_Ioc
  have hz:∀ᵐx:E∂volume,x∈O → x∉W → U x=0 := (ae_restrict_iff' hO).mp hzero
  rw [←integral_indicator hW,←integral_indicator hO]
  apply integral_congr_ae
  filter_upwards [hz] with x hx
  by_cases hxo:x∈O
  · by_cases hxw:x∈W
    · simp only [indicator_of_mem hxo,indicator_of_mem hxw]
    · simp only [indicator_of_notMem hxw,indicator_of_mem hxo,hx hxo hxw,zero_mul]
  · by_cases hxw:x∈W <;> simp [hxo,hxw]

theorem exists_nativeIncoming_potential_window_source_CLM
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (τ c:ℝ) (χ:E→ℝ) (hχ:Continuous χ) (hχrange:∀x:E,0 ≤ χ x ∧ χ x ≤ 1)
    (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1))
    (O:Set E) (hO:MeasurableSet O) (hvol:volume O < ⊤) (hOR:O⊆ball (0:E) (Real.exp c+1))
    (m:ℕ) (hm:c < (m:ℝ)/2) :
    ∃C:ℝ,0 ≤ C ∧ ∀a:ℝ,0 < a → (∀x∈O,a • x∈K) →
      ∃T:H1Zero g.leviCivitaData univ →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ),
        ‖T‖ ≤ C*Real.exp (-Real.log a/2) ∧
        (∀W,∀ᵐt:ℝ∂volume,t < -(m:ℝ)/2-1 → T W t=0) ∧
        ∀W (φ:E→ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) (h0:(0:E)∉tsupport φ),
          inner ℝ (T W) (nativePhysicalPairTestL2 φ hφ hc h0)=
            ∫x in O,nativeIncomingPotentialCoefficient gE a τ c χ x*
              toL2 g.leviCivitaData univ W (e (a • x))*φ x := by
  obtain ⟨D,hD,hp⟩:=exists_nativeIncoming_potential_source_CLM g hY gE e he hei hK hKs
    τ c χ hχ hχrange O hO hvol hOR
  let R:=physicalL2OuterWindowSourceCLM O hO m
  refine ⟨‖R‖*D,by positivity,fun a ha hfit=>?_⟩
  obtain ⟨P,hP,hPv⟩:=hp a ha hfit
  let T:=R.comp P
  refine ⟨T,(ContinuousLinearMap.opNorm_comp_le R P).trans
    ((mul_le_mul_of_nonneg_left hP (norm_nonneg R)).trans_eq (by ring)),
    fun W=>physicalL2OuterWindowSource_lower_support O hO m (P W),?_⟩
  intro W φ hφ hc h0
  have hz:∀ᵐx:E∂volume.restrict O,x∉nativePolarTimeWindow (Ioc (-(m:ℝ)/2) 0) → P W x=0 := by
    filter_upwards [hPv W] with x hx
    intro hnot
    rw [hx,nativeIncomingPotentialCoefficient_zero_outside_window gE a τ c h1 m hm hnot,zero_mul]
  exact (physicalL2OuterWindowSource_whole_physical_test O hO m (P W) hz φ hφ hc h0).trans
    (integral_congr_ae ((hPv W).mono fun x hx=>congrArg (fun v:ℝ=>v*φ x) hx))

#print axioms nativeIncomingPotentialCoefficient_zero_outside_window
#print axioms physicalL2OuterWindowSource_whole_physical_test
#print axioms exists_nativeIncoming_potential_window_source_CLM
end Yamabe3.Analysis.SpherePolar
