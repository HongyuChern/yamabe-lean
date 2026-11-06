import Yamabe3.Analysis.ChartPiecewiseSource
import Yamabe3.Analysis.NativeChartWeightedSourceBound
import Yamabe3.Analysis.LocalFlatTransmissionH4Estimate

/-! Quantitative H4 transmission in the actual smooth native chart.
The same locally H2 field solves the native divergence equation with two
original physical H2 source pieces. The actual density ratio, weak equation
transport and all source extensions are produced internally. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold
namespace Yamabe3.Analysis.UniformElliptic
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_native_chart_transmission_H4_estimate
    (g : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O V U W D Ω : Set E}
    (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O)
    (hU : IsOpen U) (hUc : IsCompact (closure U)) (hOU : closure O⊆U)
    (hUs : closure U⊆e.source) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (heW : e '' closure U⊆W) (hWD : closure W⊆D)
    (hflat : ∀ x∈e.source,e x∈Ω ↔ 0<x 0)
    (B : SmoothEllipticBilinearForm 3 univ)
    (hBU : EqOn B.a (divergenceCoefficients g e) U) :
    ∃ C : ℝ≥0∞,C≠⊤ ∧ ∀ u fpos fneg : E → ℝ,
      MemWkpLocally 2 u D → MemWkp 2 2 fpos W → MemWkp 2 2 fneg W →
      (weakDivergenceSource W (nativeDivergenceMatrix g) u =ᵐ[volume.restrict W]
        physicalSplitSource Ω fpos fneg) →
      MemWkp 4 2 (u∘e) (V∩halfSpace 3) ∧
      iteratedWeakSobolevNorm 4 2 (u∘e) (V∩halfSpace 3) ≤ C *
        (iteratedWeakSobolevNorm 2 2 u W+
          (iteratedWeakSobolevNorm 2 2 fpos W+iteratedWeakSobolevNorm 2 2 fneg W)) := by
  have hOs : closure O⊆e.source := hOU.trans (subset_closure.trans hUs)
  have heOW : e '' closure O⊆W := (image_mono (hOU.trans subset_closure)).trans heW
  obtain ⟨P,hP,hp⟩ := exists_euclidean_chart_source_bound 2 e he hei hO hOc hOs hW heOW
  obtain ⟨S,hS,hs⟩ := exists_native_chart_density_ratio_source_bound 2 g e he hei hU hUc hUs hW heW
  obtain ⟨A,hA,ha⟩ := exists_local_flat_transmission_H4_estimate B hO hOc hV hVc hVO hU hOU
  refine ⟨A*(P+S),by finiteness,?_⟩
  intro u fpos fneg hu hfpos hfneg hsource
  have huW := memWkp_on_precompact_of_locally hu hW hWc hWD
  have hc := native_weak_chart_divergence g e he hei hO hOc hOs hW hWc heOW hWD
    hU (subset_closure.trans hOU) B.a B.smooth_a hBU hu
  have heqsrc := euclidean_chart_comp_congr_ae_restrict e he hei hO hW
    (subset_closure.trans hOs) (fun x hx => heOW (mem_image_of_mem e (subset_closure hx))) hsource
  let Fpos : E → ℝ := fun x => nativeChartDensityRatio g e x*fpos (e x)
  let Fneg : E → ℝ := fun x => nativeChartDensityRatio g e x*fneg (e x)
  have hsrc : weakDivergenceSource O B.a (u∘e) =ᵐ[volume.restrict O] flatSplitSource Fpos Fneg := by
    have ht := weighted_chart_piecewise_eq hO e
      (fun x hx => hflat x (hOs (subset_closure hx))) (nativeChartDensityRatio g e) fpos fneg
    filter_upwards [hc.2,heqsrc,ht] with x hx hy hz
    exact hx.trans ((congrArg (nativeChartDensityRatio g e x*·) hy).trans hz)
  have hweak := weakEquation_weakDivergenceSource hO B.a B.smooth_a hc.1
  have hh := ha (u∘e) Fpos Fneg hc.1 (hs fpos hfpos).1 (hs fneg hfneg).1 (by
    intro φ hφ hφc hφs
    have ht := hweak φ hφ hφc hφs
    simp only [matrixFlux,Finset.sum_mul,partialDeriv] at ht
    exact ht.trans (integral_congr_ae (hsrc.mono (fun x hx => congrArg (·*φ x) hx))))
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ A*(P*iteratedWeakSobolevNorm 2 2 u W+
        S*(iteratedWeakSobolevNorm 2 2 fpos W+iteratedWeakSobolevNorm 2 2 fneg W)) := by
      rw [mul_add S]
      exact mul_le_mul le_rfl (add_le_add (hp u huW).2
        (add_le_add (hs fpos hfpos).2 (hs fneg hfneg).2)) zero_le zero_le
    _ ≤ A*((P+S)*(iteratedWeakSobolevNorm 2 2 u W+
        (iteratedWeakSobolevNorm 2 2 fpos W+iteratedWeakSobolevNorm 2 2 fneg W))) := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      rw [mul_add (P+S)]
      exact add_le_add (mul_le_mul (le_add_right le_rfl) le_rfl zero_le zero_le)
        (mul_le_mul (le_add_left le_rfl) le_rfl zero_le zero_le)
    _ = _ := (mul_assoc _ _ _).symm

#print axioms exists_native_chart_transmission_H4_estimate
end Yamabe3.Analysis.UniformElliptic
