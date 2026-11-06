import Yamabe3.Analysis.NativeJacobianC2

/-! The produced bounded solver has the literal native Levi-Civita
Jacobian of its same rescaled field and background. Low entrance values
remain explicit; this does not assert their cancellation or matching. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E3) 1 \ {(0:E3)}
local notation "P" => ({(0:E3)}ᶜ : Set E3)

theorem exists_uniform_actual_native_same_source_solver
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
              MemWkp 4 2 F U ∧
              (fun x=>ε^2*(g a).pullbackVolumeDensity id (ε • x)*
                (-8*(g a).leviCivitaData.laplacian (fun y=>F (ε⁻¹ • y)) (ε • x)+
                  ((g a).leviCivitaData.scalarCurvature (ε • x)-
                    30*radialProfile p.orbit (p.phase+Real.log ε) ‖ε • x‖^4)*F x))
                =ᵐ[volume.restrict U]
                halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) := by
  obtain ⟨M,δ,hM,hδ,hR⟩:=exists_uniform_native_same_source_H4_solver hκ0 hκ1 Λ g hB hρ
  refine ⟨M,δ,hM,hδ,?_⟩
  intro ε hε hεδ a ha p
  obtain ⟨R,E,hRM,hE,hRf⟩:=hR ε hε hεδ a ha p
  refine ⟨R,E,hRM,hE,?_⟩
  intro f
  obtain ⟨F,hFc,hF2,hF0,hFv,hFa,hFb,hFp⟩:=hRf f
  refine ⟨F,hFc,hF2,hF0,hFv,hFa,hFb,?_⟩
  intro U hU hUc hUO
  obtain ⟨hF4,heq⟩:=hFp U hU hUc hUO
  refine ⟨hF4,?_⟩
  filter_upwards [heq,ae_restrict_mem hU.measurableSet] with x he hx
  have hx0:x≠0:=(hUO (subset_closure hx)).2
  have hi:=native_same_scaled_field_actual_jacobian (g a) p.orbit p.phase hε
    (hF2.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx0)) hx0
  rw [hi] at he
  nlinarith

#print axioms exists_uniform_actual_native_same_source_solver
end Yamabe3.Analysis.UniformElliptic
