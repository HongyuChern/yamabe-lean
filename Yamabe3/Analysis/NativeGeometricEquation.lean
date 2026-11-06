import Yamabe3.Analysis.NativeGeometricGraphSolver
import Yamabe3.Analysis.FiniteRegularityWeakJets

/-! Cancellation of the actual native-minus-model error on the very
same C2 field. The source normalization is literal: physical source/8
is radialScale times the retained source graph value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E3) 1 \ {(0:E3)}
local notation "P" => ({(0:E3)}ᶜ : Set E3)

theorem weakNegativeLaplacian_eq_classical_C2
    {U W:Set E3} (hU:IsOpen U) (hUc:IsCompact (closure U)) (hW:IsOpen W)
    (hUW:closure U⊆W) {F:E3→ℝ} (hF:ContDiffOn ℝ 2 F W) (hF2:MemWkp 2 2 F U) :
    weakNegativeLaplacian U F =ᵐ[volume.restrict U] principalSource (fun _=>1) F := by
  have hflux (i:Fin 3):matrixFlux (fun _:E3=>(1:Matrix (Fin 3) (Fin 3) ℝ))
      (fun j=>partialDeriv j F) i=partialDeriv i F:=by
    funext x
    simp [matrixFlux,Matrix.one_apply]
  filter_upwards [eventually_all.mpr (fun i:Fin 3=>
    chosenWeakSecond_classical_on_precompact hU hUc hW hUW hF hF2 i i)] with x hx
  simp only [weakNegativeLaplacian,iterWeakPartial_succ,iterWeakPartial_zero,principalSource,hflux,hx]

theorem nativeNormalizedFullError_eq_of_eventuallyEq (g:RiemannianMetric 3 E3)
    (ε:ℝ) (v:ℝ→ℝ) (τ:ℝ) {u w:E3→ℝ} {x:E3} (h:u =ᶠ[𝓝 x] w) :
    nativeNormalizedFullError g ε v τ u x=nativeNormalizedFullError g ε v τ w x := by
  unfold nativeNormalizedFullError nativeNormalizedPotentialError nativeNormalizedPrincipalError nativePrincipalError
  rw [h.self_of_nhds,principalSource_eq_of_eventuallyEq _ h]

theorem native_geometric_fixed_point_equation
    (g:RiemannianMetric 3 E3) {ε:ℝ} (hε:0<ε) {κ:ℝ} (p:DelaunayPhaseData κ)
    (f:HalfEndPhysicalH2SourceGraph) (v:HalfEndPhysicalH4Graph)
    (T:HalfEndPhysicalH4Graph→L[ℝ]HalfEndPhysicalH2SourceGraph)
    (hT:∀x:HalfEndSourceEntrance,halfEndPhysicalH2SourceGraphValue (T v) x=
      nativeNormalizedFullError g ε p.orbit p.phase (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x)
    {F:E3→ℝ} (hF:ContDiffOn ℝ 2 F P)
    (hv:EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) F (closedBall (0:E3) 4))
    {U:Set E3} (hU:IsOpen U) (hUc:IsCompact (closure U)) (hUO:closure U⊆O)
    (hF4:MemWkp 4 2 F U)
    (heq:weakNegativeLaplacian U F =ᵐ[volume.restrict U]
      (fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue (f-T v)) x/8+
        nativeHalfEndPotentialCoefficient p.potential x*F x)) :
    nativeRescaledDelaunayJacobian g ε p.orbit p.phase F =ᵐ[volume.restrict U]
      (fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8) := by
  have hclass:=weakNegativeLaplacian_eq_classical_C2 hU hUc isClosed_singleton.isOpen_compl
    (fun x hx=>(hUO hx).2) hF (hF4.le_of_le (by norm_num))
  filter_upwards [heq,hclass,ae_restrict_mem hU.measurableSet] with x he hc hx
  have hxO:=hUO (subset_closure hx)
  have hx0:x≠0:=hxO.2
  have hx1:‖x‖<1:=by simpa only [mem_ball,dist_zero_right] using hxO.1
  have hxsrc:x≠0 ∧ ‖x‖≤3:=⟨hx0,by linarith⟩
  have hgerm:halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) =ᶠ[𝓝 x] F:=by
    filter_upwards [isOpen_ball.mem_nhds (show x∈ball (0:E3) 4 by simpa using (show ‖x‖<4 by linarith))] with y hy
    exact hv (Metric.ball_subset_closedBall hy)
  have herror:halfEndSourceExtension (halfEndPhysicalH2SourceGraphValue (T v)) x=
      nativeNormalizedFullError g ε p.orbit p.phase F x:=by
    rw [halfEndSourceExtension_of_mem _ hxsrc,hT]
    exact nativeNormalizedFullError_eq_of_eventuallyEq g ε p.orbit p.phase hgerm
  have hsub:halfEndSourceExtension (halfEndPhysicalH2SourceGraphValue (f-T v)) x=
      halfEndSourceExtension (halfEndPhysicalH2SourceGraphValue f) x-
      halfEndSourceExtension (halfEndPhysicalH2SourceGraphValue (T v)) x:=by
    rw [map_sub]
    exact map_sub (halfEndSourceEval x) _ _
  have hid:=nativeNormalizedFullError_eq_operator_difference_C2_at g hε p.orbit p.phase hx0
    (hF.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx0))
  have hpot:=congrFun (fullModelPotential_eq_neg_annular p) x
  rw [hc] at he
  unfold halfEndEuclideanPhysicalSource at he ⊢
  rw [hsub,herror] at he
  unfold flatDelaunayJacobian at hid
  change nativeHalfEndPotentialCoefficient p.potential x= -annularDelaunayPotential p.orbit p.phase x at hpot
  rw [hpot] at he
  nlinarith

#print axioms weakNegativeLaplacian_eq_classical_C2
#print axioms nativeNormalizedFullError_eq_of_eventuallyEq
#print axioms native_geometric_fixed_point_equation
end Yamabe3.Analysis.UniformElliptic
