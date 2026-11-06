import Yamabe3.Analysis.NativeFullErrorGraph
import Yamabe3.Analysis.UniformElliptic.NativeDelaunayOperatorError

/-! The completed graph operator represents the actual native-minus-model
Jacobian difference on the same C2 function. No smoothness assumption is
added to the original H4 graph. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem principalSource_sub_coefficients_C2_at
    (a b : E → Matrix (Fin 3) (Fin 3) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun z => a z i j))
    (hb : ∀ i j, ContDiff ℝ ∞ (fun z => b z i j))
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    principalSource (fun y => a y-b y) u x = principalSource a u x-principalSource b u x := by
  let F := matrixFlux a (fun j => partialDeriv j u)
  let G := matrixFlux b (fun j => partialDeriv j u)
  have hp (j : Fin 3) : DifferentiableAt ℝ (partialDeriv j u) x :=
    ((hu.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hF (i : Fin 3) : DifferentiableAt ℝ (F i) x := by
    change DifferentiableAt ℝ (fun y => ∑ j : Fin 3, a y i j*partialDeriv j u y) x
    exact DifferentiableAt.fun_sum (fun j _ => ((ha i j).differentiable (by simp) x).mul (hp j))
  have hG (i : Fin 3) : DifferentiableAt ℝ (G i) x := by
    change DifferentiableAt ℝ (fun y => ∑ j : Fin 3, b y i j*partialDeriv j u y) x
    exact DifferentiableAt.fun_sum (fun j _ => ((hb i j).differentiable (by simp) x).mul (hp j))
  have hflux (i : Fin 3) : matrixFlux (fun y => a y-b y) (fun j => partialDeriv j u) i =
      fun y => F i y-G i y := by
    funext y
    simp only [matrixFlux,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib,F,G]
  have hpart (i : Fin 3) : partialDeriv i (fun y => F i y-G i y) x =
      partialDeriv i (F i) x-partialDeriv i (G i) x := by
    change (fderiv ℝ (fun y => F i y-G i y) x) (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_sub (hF i) (hG i)]
    rfl
  simp only [principalSource,hflux,hpart,Finset.sum_sub_distrib]
  change -((∑ i : Fin 3, partialDeriv i (F i) x)-∑ i : Fin 3, partialDeriv i (G i) x) = _
  ring

theorem nativeNormalizedFullError_eq_operator_difference_C2_at
    (g : RiemannianMetric 3 E) {ε : ℝ} (hε : 0 < ε) (v : ℝ → ℝ) (τ : ℝ)
    {u : E → ℝ} {x : E} (hx : x ≠ 0) (hu : ContDiffAt ℝ 2 u x) :
    radialScale ‖x‖*nativeNormalizedFullError g ε v τ u x =
      nativeRescaledDelaunayJacobian g ε v τ u x-flatDelaunayJacobian v τ u x := by
  have hcoeff := principalSource_sub_coefficients_C2_at
    (fun y => nativeDivergenceMatrix g (ε • y)) (fun _ => 1)
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul ε))
    (fun _ _ => contDiff_const) hu
  unfold nativeNormalizedFullError nativeNormalizedPotentialError nativeNormalizedPrincipalError nativePrincipalError
  rw [hcoeff,nativeRescaledDelaunayJacobian,rescaledNativeJacobianPotential_delaunay g hε v τ hx,flatDelaunayJacobian]
  field_simp [(radialScale_pos ‖x‖).ne']
  <;> ring

theorem nativeNormalizedFullError_graph_identity
    (g : RiemannianMetric 3 E) {ε : ℝ} (hε : 0 < ε) {κ : ℝ} (p : DelaunayPhaseData κ)
    (v : HalfEndPhysicalH4Graph) (x : HalfEndSourceEntrance) :
    radialScale ‖(x:E)‖*nativeNormalizedFullError g ε p.orbit p.phase
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x =
    nativeRescaledDelaunayJacobian g ε p.orbit p.phase
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x-
    flatDelaunayJacobian p.orbit p.phase
      (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x := by
  have hx : (x:E) ∈ ball (0:E) 4 \ {(0:E)} :=
    ⟨by simpa only [mem_ball,dist_zero_right] using lt_of_le_of_lt x.2.2 (by norm_num : (3:ℝ)<4),x.2.1⟩
  exact nativeNormalizedFullError_eq_operator_difference_C2_at g hε p.orbit p.phase x.2.1
    ((halfEndPhysicalH4Graph_contDiffOn_two v).contDiffAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hx))

#print axioms principalSource_sub_coefficients_C2_at
#print axioms nativeNormalizedFullError_eq_operator_difference_C2_at
#print axioms nativeNormalizedFullError_graph_identity
end Yamabe3.Analysis.UniformElliptic
