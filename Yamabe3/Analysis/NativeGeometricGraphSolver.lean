import Yamabe3.Analysis.SmallErrorBoundedSolver
import Yamabe3.Analysis.NativeFullErrorIdentityC2

/-! The actual fixed-version full-source model solver and actual small
native-minus-flat graph error produce a uniformly bounded geometric
fixed point. No error-range high-mode assumption is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E3) 1 \ {(0:E3)}
local notation "P" => ({(0:E3)}ᶜ : Set E3)

theorem exists_uniform_native_geometric_graph_solver
    {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) {ι:Type*} (Λ:Finset ι)
    (g:ι→RiemannianMetric 3 E3)
    (hB:∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ:∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃M δ:ℝ,0≤M ∧ 0<δ ∧ ∀ε:ℝ,0<ε→ε<δ→∀a∈Λ,∀p:DelaunayPhaseData κ,
      ∃ (R:HalfEndPhysicalH2SourceGraph→L[ℝ]HalfEndPhysicalH4Graph)
        (E:HalfEndPhysicalH4Graph→L[ℝ]HalfEndPhysicalH2SourceGraph),
        ‖R‖≤M ∧
        (∀(v:HalfEndPhysicalH4Graph) (x:HalfEndSourceEntrance),
          halfEndPhysicalH2SourceGraphValue (E v) x=nativeNormalizedFullError (g a) ε p.orbit p.phase
            (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) x) ∧
        ∀f:HalfEndPhysicalH2SourceGraph,
          let h:=f-E (R f)
          ∃F:E3→ℝ,Continuous F ∧ ContDiffOn ℝ 2 F P ∧ F 0=0 ∧
            EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (R f))) F (closedBall (0:E3) 4) ∧
            (F =ᵐ[volume.restrict O] fullModelPhysicalField hκ0 hκ1 p h) ∧
            (∀b:E3,‖b‖=1→F b=fullModelEntranceLift p h b) ∧
            ∀U:Set E3,IsOpen U→IsCompact (closure U)→closure U⊆O→
              MemWkp 4 2 F U ∧ weakNegativeLaplacian U F =ᵐ[volume.restrict U]
                (fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue h) x/8+
                  nativeHalfEndPotentialCoefficient p.potential x*F x) := by
  obtain ⟨C,hC,hT⟩:=exists_uniform_full_true_entrance_H4_solver hκ0 hκ1
  let η:ℝ:=1/(2*(C+1))
  have hη:0<η:=by dsimp only [η];positivity
  obtain ⟨δ,hδ,hErr⟩:=exists_small_native_full_error_graph_operator Λ g hB hρ hη
  refine ⟨2*C,δ,by positivity,hδ,?_⟩
  intro ε hε hεδ a ha p
  obtain ⟨T,hTC,hTf⟩:=hT p
  obtain ⟨E,hE,hEv⟩:=hErr ε hε.le hεδ a ha κ p
  have hCη:C*η≤1/2:=by
    dsimp only [η]
    have hpos:0<2*(C+1):=by positivity
    rw [one_div,←div_eq_mul_inv]
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  have hs:‖T‖*‖E‖≤1/2:=(mul_le_mul hTC hE (norm_nonneg E) hC).trans hCη
  let R:=smallErrorSolutionCLM T E hs
  refine ⟨R,E,(smallErrorSolutionCLM_norm T E hs).trans (by linarith),hEv,?_⟩
  intro f
  have he:T (f-E (R f))=R f:=smallErrorSolution_fixed T E hs f
  obtain ⟨F,hFc,hF2,hF0,hFv,hFa,hFb,hFp⟩:=hTf (f-E (R f))
  rw [he] at hFv
  exact ⟨F,hFc,hF2,hF0,hFv,hFa,hFb,hFp⟩

#print axioms exists_uniform_native_geometric_graph_solver
end Yamabe3.Analysis.UniformElliptic
