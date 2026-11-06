import Yamabe3.Analysis.NativeIncomingAnnularValue
import Yamabe3.Analysis.NativeIncomingCoreCutoff
import Yamabe3.Analysis.FullBubbleCriticalTail
import Yamabe3.Analysis.FullBubbleRegularSource
import Yamabe3.Analysis.L2BoundedScalarMultiplier

/-! The actual normalized model potential part of the incoming source.
It keeps the chart density, puncture gate and SAME bubble tail difference.
Only the native L6 value is used on the large annulus; no unproved H4
or C2 regularity outside the homogeneous core is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic Delaunay
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def incomingPotentialH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] incomingPotentialH1Normed

def nativeIncomingPotentialCoefficient (gE:RiemannianMetric 3 E) (a τ c:ℝ) (χ:E→ℝ) (x:E) : ℝ :=
  gE.pullbackVolumeDensity id (a • x)*(1-χ x)*
    (fullBubblePotentialTail τ (Real.exp c) x-fullBubbleSpatialPotential (Real.exp τ) x)

private theorem incoming_density_continuous (gE:RiemannianMetric 3 E) :
    Continuous (gE.pullbackVolumeDensity id) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (gE.contDiffAt_pullbackVolumeDensity (f:=id) (x:=x) contMDiffAt_id
    (by simpa using Function.injective_id)).1.continuousAt

theorem nativeIncomingPotentialCoefficient_zero_inner
    (gE:RiemannianMetric 3 E) (a τ c:ℝ) {χ:E→ℝ}
    (h1:∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x](fun _=>1)) {x:E} (hx:‖x‖ ≤ 2) :
    nativeIncomingPotentialCoefficient gE a τ c χ x=0 := by
  have hχ:χ x=1 := (h1 x (by simpa only [mem_closedBall,dist_zero_right] using hx)).self_of_nhds
  simp only [nativeIncomingPotentialCoefficient,hχ,sub_self,mul_zero,zero_mul]

theorem nativeIncomingPotentialCoefficient_zero_outer
    (gE:RiemannianMetric 3 E) (a τ c:ℝ) (χ:E→ℝ) {x:E} (hx:Real.exp c < ‖x‖) :
    nativeIncomingPotentialCoefficient gE a τ c χ x=0 := by
  simp [nativeIncomingPotentialCoefficient,fullBubblePotentialTail,hx]

theorem exists_nativeIncoming_potential_source_CLM
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    (τ c:ℝ) (χ:E→ℝ) (hχ:Continuous χ) (hχrange:∀x:E,0 ≤ χ x ∧ χ x ≤ 1)
    (O:Set E) (hO:MeasurableSet O) (hvol:volume O < ⊤) (hOR:O⊆ball (0:E) (Real.exp c+1)) :
    ∃C:ℝ,0 ≤ C ∧ ∀a:ℝ,0 < a → (∀x∈O,a • x∈K) →
      ∃T:H1Zero g.leviCivitaData univ →L[ℝ] Lp ℝ 2 (volume.restrict O),
        ‖T‖ ≤ C*Real.exp (-Real.log a/2) ∧ ∀W:H1Zero g.leviCivitaData univ,
          (T W:E→ℝ)=ᵐ[volume.restrict O]fun x:E=>
            nativeIncomingPotentialCoefficient gE a τ c χ x*toL2 g.leviCivitaData univ W (e (a • x)) := by
  obtain ⟨D,hD⟩:=hK.exists_bound_of_continuousOn (incoming_density_continuous gE).continuousOn
  obtain ⟨J,hJ⟩:=(isCompact_closedBall (0:E) (Real.exp c+1)).exists_bound_of_continuousOn
    (fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.continuousOn
  let C0:=max D 0*max J 0
  have hC0:0 ≤ C0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  obtain ⟨N,hN,hvalue⟩:=exists_nativeIncoming_annular_value_CLM g hY e he hei hK hKs O hvol
  refine ⟨C0*N,mul_nonneg hC0 hN,fun a ha hfit=>?_⟩
  let q:=nativeIncomingPotentialCoefficient gE a τ c χ
  have hm:Measurable q := by
    exact (((incoming_density_continuous gE).comp (continuous_const_smul a)).measurable.mul
      (measurable_const.sub hχ.measurable)).mul
      (((fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.measurable.indicator
        (measurableSet_lt measurable_const measurable_norm)).sub
          (fullBubbleSpatialPotential_smooth (Real.exp_pos τ)).continuous.measurable)
  have hq:∀ᵐx:E∂volume.restrict O,‖q x‖ ≤ C0 := by
    filter_upwards [ae_restrict_mem hO] with x hx
    have hρb:‖gE.pullbackVolumeDensity id (a • x)‖ ≤ max D 0 := (hD (a • x) (hfit x hx)).trans (le_max_left _ _)
    have hqb:‖fullBubbleSpatialPotential (Real.exp τ) x‖ ≤ max J 0 :=
      (hJ x (ball_subset_closedBall (hOR hx))).trans (le_max_left _ _)
    have hgate:‖1-χ x‖ ≤ 1 := by rw [Real.norm_eq_abs];exact abs_le.mpr ⟨by linarith [(hχrange x).2],by linarith [(hχrange x).1]⟩
    have hdiff:‖fullBubblePotentialTail τ (Real.exp c) x-fullBubbleSpatialPotential (Real.exp τ) x‖ ≤ max J 0 := by
      by_cases ht:Real.exp c < ‖x‖
      · simpa [fullBubblePotentialTail,ht] using (le_max_right J (0:ℝ))
      · simpa [fullBubblePotentialTail,ht] using hqb
    change ‖nativeIncomingPotentialCoefficient gE a τ c χ x‖ ≤ _
    rw [nativeIncomingPotentialCoefficient,norm_mul,norm_mul]
    exact (mul_le_mul (mul_le_mul hρb hgate (norm_nonneg _) (le_max_right _ _)) hdiff
      (norm_nonneg _) (by positivity)).trans_eq (by dsimp only [C0];ring)
  let A:=l2ScalarMulCLM q hm.aestronglyMeasurable C0 hC0 hq
  have hA:‖A‖ ≤ C0 := A.opNorm_le_bound hC0 (fun v=>l2ScalarMul_norm_le q hm.aestronglyMeasurable C0 hC0 hq v)
  obtain ⟨V,hV,hVv⟩:=hvalue a ha
  let T:=A.comp V
  refine ⟨T,(ContinuousLinearMap.opNorm_comp_le A V).trans
    ((mul_le_mul hA hV (norm_nonneg V) hC0).trans_eq (by ring)),?_⟩
  intro W
  filter_upwards [l2ScalarMul_ae q hm.aestronglyMeasurable C0 hC0 hq (V W),hVv W,ae_restrict_mem hO] with x hx hv hxO
  change l2ScalarMul q hm.aestronglyMeasurable C0 hC0 hq (V W) x=_
  rw [hx,hv,nativeCoordinateZeroPullback,indicator_of_mem (hfit x hxO)]

#print axioms nativeIncomingPotentialCoefficient_zero_inner
#print axioms nativeIncomingPotentialCoefficient_zero_outer
#print axioms exists_nativeIncoming_potential_source_CLM
end Yamabe3.Analysis.SpherePolar
