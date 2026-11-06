import Yamabe3.Analysis.NativeH4GraphCouplingBounds

/-! The graph trace equals the literal trace of the same C2 solution.
The normal identity uses an actual neighborhood equality, never a
restriction of a volume-a.e. equality to the sphere. The matching witness
is identified by injectivity and the proved coupled inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff Manifold lp RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay

theorem nativeH4Graph_trace_agrees_C2 (v : HalfEndPhysicalH4Graph) (u : nativeC2OffZero)
    (hu : EqOn (nativeH4GraphFunction v) u.val (closedBall (0:E) 4)) :
    nativeH4GraphAngularValueCLM v=nativeTraceAngularCLM (nativeCollarValueTraceCLM (nativeC2CollarJetInclusion u)) ∧
    nativeH4GraphAngularNormalCLM v=nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeC2CollarJetInclusion u)) := by
  have hg (θ : S) : nativeH4GraphFunction v=ᶠ[𝓝 (θ:E)] u.val := by
    filter_upwards [isOpen_ball.mem_nhds (nativeH4Graph_sphere_mem θ).1] with x hx
    exact hu (ball_subset_closedBall hx)
  rw [nativeC2_value_trace_angular,nativeC2_normal_trace_angular]
  constructor
  · change nativeSphereL2Inclusion (nativeH4GraphSphereValueCLM v)=_
    rw [nativeSphereL2Inclusion_eq_continuousAngularL2]
    have he : (nativeH4GraphSphereValueCLM v : S→ℝ)=(fun θ : S => u.val (θ:E)) :=
      funext (fun θ => (hg θ).self_of_nhds)
    simp only [he]
  · change nativeSphereL2Inclusion (nativeH4GraphSphereNormalCLM v)=_
    rw [nativeSphereL2Inclusion_eq_continuousAngularL2]
    have he : (nativeH4GraphSphereNormalCLM v : S→ℝ)=(fun θ : S => fderiv ℝ u.val (θ:E) (θ:E)) := by
      funext θ
      exact congrArg (fun L : E→L[ℝ]ℝ => L (θ:E)) ((hg θ).fderiv_eq)
    simp only [he]

theorem nativeH4Graph_coupled_witness_identity (B P : NativeHighPotential)
    (v : HalfEndPhysicalH4Graph) (u : nativeC2OffZero)
    (hu : EqOn (nativeH4GraphFunction v) u.val (closedBall (0:E) 4))
    (d σ : AngularH1)
    (hd : angularEmbedding d=nativeHighProjection (nativeTraceAngularCLM (nativeCollarValueTraceCLM (nativeC2CollarJetInclusion u))))
    (hσ : nativeHighEnergyProjectionCLM σ=σ)
    (hc : B.dtn (σ+d)+P.dtn σ=
      -nativeHighProjection (nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeC2CollarJetInclusion u)))-
        (1/2:ℝ) • angularEmbedding d) :
    d=nativeH4GraphHighValueCLM v ∧ σ=nativeH4GraphSigmaCLM B P v := by
  have ht := nativeH4Graph_trace_agrees_C2 v u hu
  have hd' : d=nativeH4GraphHighValueCLM v := by
    apply angularEmbedding_injective
    change angularEmbedding d=angularEmbedding (nativeH4GraphHighValue v)
    rw [nativeH4GraphHighValue_embedding,ht.1,hd]
  refine ⟨hd',?_⟩
  have he : (B.dtn+P.dtn) σ=nativeH4GraphNormalJumpCLM v-B.dtn (nativeH4GraphHighValueCLM v) := by
    rw [←ht.2,hd',map_add] at hc
    change B.dtn σ+P.dtn σ=_
    change B.dtn σ+B.dtn (nativeH4GraphHighValueCLM v)+P.dtn σ=nativeH4GraphNormalJumpCLM v at hc
    calc
      _=(B.dtn σ+B.dtn (nativeH4GraphHighValueCLM v)+P.dtn σ)-B.dtn (nativeH4GraphHighValueCLM v) := by abel
      _=_ := by rw [hc]
  have h := congrArg (nativeHighCoupledDtNInverse B P) he
  rwa [nativeHighCoupledDtNInverse_left,hσ] at h

#print axioms nativeH4Graph_trace_agrees_C2
#print axioms nativeH4Graph_coupled_witness_identity
end Yamabe3.Analysis.UniformElliptic
