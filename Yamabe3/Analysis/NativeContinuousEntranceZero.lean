import Yamabe3.Analysis.NativeDelaunayEntranceWitness
import Yamabe3.Analysis.ContinuousZeroBoundaryH4
import Yamabe3.Analysis.NativeBoundedH4Solver
import Yamabe3.Analysis.EuclideanChartAE

/-! The continuous same-source representative vanishes pointwise at the
actual unit-sphere entrance. The proof passes through genuine W01,2
localization, local H4 regularity and continuous zero extension. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff Manifold BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 1 \ {(0:E)}

theorem native_continuous_same_source_entrance_zero
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (p : DelaunayPhaseData κ)
    (f : HalfEndHighH2Source) {F : E → ℝ} (hF : Continuous F)
    (hForig : F =ᵐ[volume.restrict O]
      cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg f)) :
    ∀ a : E, ‖a‖ = 1 → F a = 0 := by
  intro a ha
  obtain ⟨e,χ,U,C,hae,haU,hU,hUc,hUs,het,he,hei,hflat,hone,hface,hχ,hc,hs,hC,hb⟩ :=
    exists_uniform_delaunay_entrance_chart_H4_witness hκ0 hκ1 a ha
  let z := delaunayPhaseCompletion hκ0 hκ1 p f
  have hreg := hb p.orbit p.smooth (fun t => ⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩)
    p.ode p.phase p.potential (fun t => rfl) p.kernel_bound p.potential_nonneg p.potential_smooth f
  have hz := nativeHalfEndH2SourceCompletion_rep hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg p.potential_smooth f
  have hind : (O).indicator F =ᵐ[volume] toL2 nativeWeakEuclideanD O z := by
    have hh := (ae_restrict_iff' (isOpen_ball.sdiff isClosed_singleton).measurableSet).mp hForig
    filter_upwards [hz,hh] with x hx hf
    dsimp only [z,delaunayPhaseCompletion]
    rw [hx]
    by_cases hxo : x ∈ O
    · simp only [indicator_of_mem hxo]
      exact hf hxo
    · simp only [indicator_of_notMem hxo]
  have hUs' : U ⊆ e.source := subset_closure.trans hUs
  have hcomp := euclidean_chart_comp_congr_ae e he hei hind
  have hlocal : (fun x => F (e x)) =ᵐ[volume.restrict (U ∩ {x:E | 0 < x 0})]
      chartPullback e (fun y => χ y * toL2 nativeWeakEuclideanD O z y) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans hUs') hcomp,
      ae_restrict_mem (hU.inter Poincare.Analysis.Sobolev.BoundaryTangential.isOpen_halfSpace).measurableSet]
      with x hx hxU
    have hxs := hUs' hxU.1
    have hxo := (hflat x hxs).mpr hxU.2
    rw [indicator_of_mem hxo] at hx
    rw [chartPullback_apply e _ hxs,hone x hxU.1,one_mul]
    exact hx
  have hzero := continuous_boundary_zero_of_memW01p_local_H4 hU
    (Boundary.memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat z)
    hreg.1 (hF.comp_continuousOn (e.continuousOn.mono hUs')) hlocal haU hface
  simpa only [Function.comp_apply,e.right_inv hae] using hzero

#print axioms native_continuous_same_source_entrance_zero
end Yamabe3.Analysis.UniformElliptic
