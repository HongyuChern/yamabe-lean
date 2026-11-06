import Yamabe3.Analysis.WeakVariableEquationH4Estimate
import Yamabe3.Analysis.NativeCorrectedInteriorH4
import Yamabe3.Analysis.UniformElliptic.NativeScaledCoefficients

/-! The actual native weak equation has an interior H4 estimate uniform
before the scale, Delaunay orbit, phase, source and solution. The radius
and constant depend only on the fixed normalized metric and the fixed
nested annuli. The original source and actual divergence operator are
retained; no estimate or replacement equation is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_native_weak_H4_estimate
    (g : RiemannianMetric 3 E3) (hB : g.euclideanCoefficients 0 = innerSL ℝ)
    (hρ : g.pullbackVolumeDensity id 0 = 1)
    {O V W : Set E3} (hO : IsOpen O) (hO0 : ∀x∈O,x≠0)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hVann : ∀x∈V,(1/2:ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃δ : ℝ,0<δ ∧ ∃C : ℝ≥0∞,C≠⊤ ∧ ∀r : ℝ,0≤r → r<δ →
      ∀v : ℝ→ℝ,ContDiff ℝ ∞ v →
      (∀t,0≤v t ∧ v t≤1 ∧ |deriv v t|≤1/2) →
      (∀t,deriv (deriv v) t=radialForce (v t)) →
      ∀(τ : ℝ) (u F : E3→ℝ),MemWkpLocally 4 u O → MemWkp 2 2 F V →
      nativeWeakRescaledDelaunayJacobian V g r v τ u=ᵐ[volume.restrict V] F →
      MemWkp 4 2 u W ∧ iteratedWeakSobolevNorm 4 2 u W ≤ C*
        (iteratedWeakSobolevNorm 0 2 u V+iteratedWeakSobolevNorm 2 2 F V) := by
  obtain ⟨δ₁,hδ₁,L,hL,hform⟩ := exists_uniform_native_rescaled_bilinear_forms g hB hρ 4 (by norm_num : (0:ℝ)<3)
  obtain ⟨δ₂,hδ₂,herror⟩ := exists_uniform_small_native_delaunay_potential_error g hρ 2 (by norm_num : (0:ℝ)<1)
  obtain ⟨Q,hQ,hQj⟩ := exists_uniform_delaunay_annular_potential_jets 2
  have hVball : closure V ⊆ Metric.ball (0:E3) 3 := by
    have h : V ⊆ Metric.closedBall (0:E3) 2 := fun x hx => by simpa using (hVann x hx).2
    exact (closure_minimal h Metric.isClosed_closedBall).trans (Metric.closedBall_subset_ball (by norm_num))
  obtain ⟨C,hC,hestimate⟩ := exists_uniform_weak_variable_equation_H4_estimate hV hVc hVball hW hWc hWV
    (by norm_num : (0:ℝ)<1/2) hL (by linarith : 0≤Q+1)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,C,hC,?_⟩
  intro r hr hrδ v hv hb hODE τ u F hu hF heq
  obtain ⟨B,hBa,hBell,hjet,hosc⟩ := hform r hr (hrδ.trans_le (min_le_left _ _))
  let q : E3→ℝ := fun x => -(annularDelaunayPotential v τ x+nativeDelaunayPotentialError g r v τ x)
  have hq : ContDiffOn ℝ ∞ q O := fun x hx =>
    ((contDiffAt_annularDelaunayPotential hv τ (hO0 x hx)).add
      (contDiffAt_nativeDelaunayPotentialError g r hv τ (hO0 x hx))).neg.contDiffWithinAt
  have hqj : ∀n≤2,∀x∈V,‖iteratedFDeriv ℝ n q x‖≤Q+1 := by
    intro n hn x hx
    have hx0 := hO0 x (hVO (subset_closure hx))
    change ‖iteratedFDeriv ℝ n (-(annularDelaunayPotential v τ+nativeDelaunayPotentialError g r v τ)) x‖≤Q+1
    rw [iteratedFDeriv_neg_apply,norm_neg]
    change ‖iteratedFDeriv ℝ n (fun y => annularDelaunayPotential v τ y+nativeDelaunayPotentialError g r v τ y) x‖ ≤ Q+1
    rw [fun_iteratedFDeriv_add_apply
      ((contDiffAt_annularDelaunayPotential hv τ hx0).of_le (by exact_mod_cast le_top))
      ((contDiffAt_nativeDelaunayPotentialError g r hv τ hx0).of_le (by exact_mod_cast le_top))]
    exact (norm_add_le _ _).trans (add_le_add
      (hQj v hv hb hODE τ n hn x (hVann x hx).1 (hVann x hx).2)
      (herror r hr (hrδ.trans_le (min_le_right _ _)) v hv hb hODE τ n hn x (hVann x hx).1 (hVann x hx).2))
  refine hestimate B (by rw [hBell])
    (fun n hn x hx => hjet n hn x (hVball (subset_closure hx)))
    (fun x hx => hosc x (hVball (subset_closure hx))) O hO hVO q hq hqj u F hu hF ?_
  have hw := nativeWeakJacobian_divergence_equation hV g r v τ
    ((memWkp_on_precompact_of_locally hu hV hVc hVO).le_of_le (by norm_num : 2≤4)) heq
  simpa only [WeakEquation,matrixFlux,Finset.sum_mul,hBa,nativeScaledDivergenceMatrix,q,neg_mul,sub_eq_add_neg] using hw

#print axioms exists_uniform_native_weak_H4_estimate
end Yamabe3.Analysis.UniformElliptic
