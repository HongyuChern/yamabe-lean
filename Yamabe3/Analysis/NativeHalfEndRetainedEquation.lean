import Yamabe3.Analysis.NativeHalfEndGraphCompletion

/-! The same constructed half-end completion element supplies the retained
weak-solution interface. The global L2 right-hand side is constructed by
zero extension; its normalized physical identity is proved, not assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction InnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- One z is chosen before every retained test. The source and solution
are the original graph source and its actual half-end field. -/
theorem nativeHalfEndH2Source_retained_equation
    (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t)) (f : HalfEndHighH2Source) :
    let u := cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f)
    let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    ∃ z : H1Zero D O, ∃ G : Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure,
      (toL2 D O z : E → ℝ) =ᵐ[volume] O.indicator u ∧
      (G : E → ℝ) =ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure]
        O.indicator (fun x => F x / 8 + nativeHalfEndPotentialCoefficient V x * toL2 D O z x) ∧
      (∀ v : H1Zero D O, ⟪z, v⟫_ℝ - ⟪toL2 D O z, toL2 D O v⟫_ℝ = ⟪G, toL2 D O v⟫_ℝ) ∧
      ‖z‖ ^ 2 ≤
        ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 / 6 +
          (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
            nativeHalfHighDirichletDerivativeBound κ V ^ 2) / 2) *
          ‖halfEndH2SourceToAngularCLM f.1‖ ^ 2 := by
  let u := cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f)
  let F := halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1)
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  let g : E → ℝ := fun x => F x / 8 + nativeHalfEndPotentialCoefficient V x * u x
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  obtain ⟨-, -, hg, du, z, -, hz, hzO, hvar, -, -, -, hbound, -⟩ :=
    nativeHalfEndH2Source_completion_and_model_green hκ0 hκ1 V hV hV0 hVs f
  have hG : MemLp (O.indicator g) 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure := by
    simpa only [native_euclideanMetric_volumeMeasure] using
      (memLp_indicator_iff_restrict hO.measurableSet).mpr hg
  let G : Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure := hG.toLp (O.indicator g)
  have hzO' : ∀ᵐ x ∂volume, x ∈ O → (toL2 D O z : E → ℝ) x = u x :=
    (ae_restrict_iff' hO.measurableSet).mp hzO
  have hsame : O.indicator g =ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure]
      O.indicator (fun x => F x / 8 + nativeHalfEndPotentialCoefficient V x * toL2 D O z x) := by
    simp only [native_euclideanMetric_volumeMeasure]
    filter_upwards [hzO'] with x hx
    by_cases hxO : x ∈ O
    · simp only [indicator_of_mem hxO, g, hx hxO]
    · simp only [indicator_of_notMem hxO]
  refine ⟨z, G, hz, hG.coeFn_toLp.trans hsame, ?_, hbound⟩
  intro v
  change gradientEnergy D O z v = nativeCompletionRHS hO hg v
  rw [nativeCompletionRHS_eq_integral hO hg v]
  exact (hvar v).2

#print axioms nativeHalfEndH2Source_retained_equation
end Yamabe3.Analysis.UniformElliptic
