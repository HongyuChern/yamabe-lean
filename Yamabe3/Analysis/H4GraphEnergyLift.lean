import Yamabe3.Analysis.H4GraphCompactC1Realization
import Yamabe3.Analysis.EuclideanC1EnergyFamily

/-! A single bounded H1Zero lift of EVERY original weighted H4 graph,
retaining its actual field on the inner ball. The constant is fixed
before graph values, source inputs and subsequent physical dilations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD

theorem exists_H4Graph_bounded_energy_lift :
    ∃χ:E→ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ⊆ball (0:E) 3 ∧
      (∀x∈closedBall (0:E) 2,χ=ᶠ[𝓝 x] (fun _:E => (1:ℝ))) ∧
      ∃L:HalfEndPhysicalH4Graph →L[ℝ] H1Zero D (ball (0:E) 3),
        ∀v:HalfEndPhysicalH4Graph,
          (toL2 D (ball (0:E) 3) (L v):E→ℝ)=ᵐ[volume]
            (fun x => χ x*halfEndEntranceExtension (halfEndPhysicalH4GraphValue v) x) ∧
          ‖L v‖≤‖L‖*‖v‖ := by
  obtain ⟨χ,hχ,hc,hs,h1⟩ := exists_H4_core_cutoff
  let P := H4CoreCutoffLinear χ
  let L := euclideanC1FamilyCLM (ball (0:E) 3) isOpen_ball P
    (H4CoreCutoffLinear_C1 hχ hs h1)
    (fun v => (H4CoreCutoffLinear_support hc hs v).1)
    (fun v => (H4CoreCutoffLinear_support hc hs v).2)
    (H4CoreCutoffLinear_eval_continuous χ)
  refine ⟨χ,hχ,hc,hs,h1,L,fun v => ⟨?_,L.le_opNorm v⟩⟩
  simpa only [native_euclideanMetric_volumeMeasure,L,P,H4CoreCutoffLinear,LinearMap.coe_mk,AddHom.coe_mk] using
    euclideanC1FamilyCLM_ae (ball (0:E) 3) isOpen_ball P
      (H4CoreCutoffLinear_C1 hχ hs h1)
      (fun v => (H4CoreCutoffLinear_support hc hs v).1)
      (fun v => (H4CoreCutoffLinear_support hc hs v).2)
      (H4CoreCutoffLinear_eval_continuous χ) v

#print axioms exists_H4Graph_bounded_energy_lift
end Yamabe3.Analysis.UniformElliptic
