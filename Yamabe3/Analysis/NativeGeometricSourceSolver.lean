import Yamabe3.Analysis.NativeGeometricEquation

/-! The same bounded fixed point solves the genuine density-weighted
native Jacobian with the original source, while retaining the actual
finite low entrance value of the effective source. -/
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

theorem exists_uniform_native_same_source_H4_solver
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
          ∃F:E3→ℝ,Continuous F ∧ ContDiffOn ℝ 2 F P ∧ F 0=0 ∧
            EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (R f))) F (closedBall (0:E3) 4) ∧
            (F =ᵐ[volume.restrict O] fullModelPhysicalField hκ0 hκ1 p (f-E (R f))) ∧
            (∀b:E3,‖b‖=1→F b=fullModelEntranceLift p (f-E (R f)) b) ∧
            ∀U:Set E3,IsOpen U→IsCompact (closure U)→closure U⊆O→
              MemWkp 4 2 F U ∧ nativeRescaledDelaunayJacobian (g a) ε p.orbit p.phase F
                =ᵐ[volume.restrict U]
                (fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8) := by
  obtain ⟨M,δ,hM,hδ,hR⟩:=exists_uniform_native_geometric_graph_solver hκ0 hκ1 Λ g hB hρ
  refine ⟨M,δ,hM,hδ,?_⟩
  intro ε hε hεδ a ha p
  obtain ⟨R,E,hRM,hE,hRf⟩:=hR ε hε hεδ a ha p
  refine ⟨R,E,hRM,hE,?_⟩
  intro f
  obtain ⟨F,hFc,hF2,hF0,hFv,hFa,hFb,hFp⟩:=hRf f
  refine ⟨F,hFc,hF2,hF0,hFv,hFa,hFb,?_⟩
  intro U hU hUc hUO
  obtain ⟨hF4,heq⟩:=hFp U hU hUc hUO
  exact ⟨hF4,native_geometric_fixed_point_equation (g a) hε p f (R f) E
    (hE (R f)) hF2 hFv hU hUc hUO hF4 heq⟩

#print axioms exists_uniform_native_same_source_H4_solver
end Yamabe3.Analysis.UniformElliptic
