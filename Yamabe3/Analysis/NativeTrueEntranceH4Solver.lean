import Yamabe3.Analysis.NativeContinuousEntranceZero
import Yamabe3.Analysis.NativeHalfEndWeakLaplacian

/-! A uniform bounded H2-to-H4 solution operator, with the true pointwise
unit-sphere entrance condition and the same-source physical equation.
The radius-four value coordinate and every weighted slice belong to the
original Banach graph. No H4 inverse, trace or PDE is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => ball (0:E) 1 \ {(0:E)}
local notation "P" => ({(0:E)}ᶜ : Set E)

theorem weakNegativeLaplacian_congr_ae {U : Set E} (hU : IsOpen U)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict U] v) :
    weakNegativeLaplacian U u =ᵐ[volume.restrict U] weakNegativeLaplacian U v := by
  filter_upwards [eventually_all.mpr (fun i : Fin 3 =>
    iterWeakPartial_ae_congr (by norm_num : (1:ℝ≥0∞) ≤ 2) hU 2 (fun _ : Fin 2 => i) huv)] with x hx
  simp only [weakNegativeLaplacian,hx]

theorem exists_uniform_native_true_entrance_H4_solver
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : DelaunayPhaseData κ,
      ∃ T : HalfEndHighH2Source →L[ℝ] HalfEndPhysicalH4Graph,
        ‖T‖ ≤ M ∧ ∀ f : HalfEndHighH2Source,
          ∃ F : E → ℝ, Continuous F ∧ ContDiffOn ℝ 2 F P ∧ F 0 = 0 ∧
            EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue (T f))) F (closedBall (0:E) 4) ∧
            (F =ᵐ[volume.restrict O]
              cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg f)) ∧
            (∀ a : E, ‖a‖ = 1 → F a = 0) ∧
            ∀ U : Set E, IsOpen U → IsCompact (closure U) → closure U ⊆ O →
              MemWkp 4 2 F U ∧ weakNegativeLaplacian U F =ᵐ[volume.restrict U]
                (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1) x/8+
                  nativeHalfEndPotentialCoefficient p.potential x*F x) := by
  obtain ⟨M,hM,hT⟩ := exists_uniform_native_bounded_H4_solver hκ0 hκ1
  refine ⟨M,hM,?_⟩
  intro p
  obtain ⟨T,hTM,hTf⟩ := hT p
  refine ⟨T,hTM,?_⟩
  intro f
  obtain ⟨F,hFc,hF2,hF0,hFv,hFa⟩ := hTf f
  refine ⟨F,hFc,hF2,hF0,hFv,hFa,native_continuous_same_source_entrance_zero hκ0 hκ1 p f hFc hFa,?_⟩
  intro U hU hUc hUO
  have ha := ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hUO) hFa
  obtain ⟨hu,hEq⟩ := nativeHalfEndH2Source_weakNegativeLaplacian hκ0 hκ1 p.potential
    p.kernel_bound p.potential_nonneg p.potential_smooth f hU hUc hUO
  refine ⟨(MemWkp_congr_ae (by norm_num) hU ha).mpr hu,?_⟩
  have hl := weakNegativeLaplacian_congr_ae hU ha
  filter_upwards [hl,hEq,ha] with x hx he hf
  exact hx.trans (he.trans (by rw [hf]))

#print axioms weakNegativeLaplacian_congr_ae
#print axioms exists_uniform_native_true_entrance_H4_solver
end Yamabe3.Analysis.UniformElliptic
