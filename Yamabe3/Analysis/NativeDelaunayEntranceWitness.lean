import Yamabe3.Analysis.DelaunayChartPotentialJets
import Yamabe3.Analysis.NativeHalfEndUniformCompletionBound
import Yamabe3.Analysis.NativeUnitSphereChartWitness
import Yamabe3.Analysis.NativeHalfEndCompletionBound
import Yamabe3.Analysis.NativeHalfEndSourceChart
import Yamabe3.Analysis.BoundaryChartH1Bound

/-! Entrance chart geometry and the H4 bound precede the Delaunay
orbit, phase and original high source. Actual state-flow jets and the
uniform same-completion bound supply the parameter control. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction Manifold ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => Metric.ball (0 : E) 1 \ {(0 : E)}

theorem exists_uniform_delaunay_entrance_chart_H4_witness
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (a : E) (ha : ‖a‖ = 1) :
    ∃ (e : OpenPartialHomeomorph E E) (χ : E → ℝ) (U : Set E) (C : ℝ≥0∞),
      a ∈ e.target ∧ e.symm a ∈ U ∧ IsOpen U ∧ IsCompact (closure U) ∧
      closure U ⊆ e.source ∧ e.target ⊆ halfEndSourceAnnulus ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      (∀ x ∈ e.source, e x ∈ O ↔ 0 < x 0) ∧
      (∀ x ∈ U, χ (e x) = 1) ∧ (e.symm a) 0 = 0 ∧
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ e.target ∧ C ≠ ⊤ ∧
      ∀ (v : ℝ → ℝ), ContDiff ℝ ∞ v →
        (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
        (∀ t, deriv (deriv v) t = radialForce (v t)) →
        ∀ (τ : ℝ) (V₀ : ℝ →ᵇ ℝ), (∀ t, V₀ t = (15/4)*v (t+τ)^4) →
        ∀ (hV₀ : ∀ t, (∫ s : ℝ, spectralMajorant (5/2) (-2) s*|V₀ (t-s)|) ≤ κ)
          (hVnonneg : ∀ t, 0 ≤ V₀ t) (hVs : ContDiff ℝ ∞ (fun t : ℝ => V₀ t))
          (f : HalfEndHighH2Source),
        let z := nativeHalfEndH2SourceCompletion hκ0 hκ1 V₀ hV₀ hVnonneg hVs f
        MemWkp 4 2 (chartPullback e (fun y => χ y * toL2 nativeWeakEuclideanD O z y))
          (U ∩ {x : E | 0 < x 0}) ∧
        iteratedWeakSobolevNorm 4 2 (chartPullback e (fun y => χ y * toL2 nativeWeakEuclideanD O z y))
          (U ∩ {x : E | 0 < x 0}) ≤ C * ENNReal.ofReal ‖f.1‖ := by
  obtain ⟨e, χ, W, U, hae, het, haU, hW, hWc, hWs, hU, hUc, hUW,
    he, hei, hχ, hc, hs, hone, hflat, hface⟩ := exists_unitSphere_chart_data_with_face a ha
  have hzero : ∀ x ∈ e.target, x ≠ 0 := by
    intro x hx hz
    have hn := (het hx).1
    simp only [hz,norm_zero] at hn
    norm_num at hn
  obtain ⟨M,hM,hMj⟩ := exists_uniform_delaunay_chart_potential_jets e he hei hzero hWc hWs 2
  have heW : e '' closure W ⊆ halfEndSourceAnnulus := by
    rintro y ⟨x, hx, rfl⟩
    exact het (e.map_source (hWs hx))
  obtain ⟨K, hK, hb⟩ := exists_chart_H4_with_uniform_physical_potential_bound (D := nativeWeakEuclideanD)
    e he hei χ hχ hc hs hflat hW hWc hWs hone hU hUc hUW
    halfEndSourceAnnulus_isOpen heW hM
  obtain ⟨C₁, hC₁, h1⟩ := QuantitativeChart.exists_chart_first_sobolev_bound (D := nativeWeakEuclideanD)
    e he hei χ hχ hc hs hflat
  obtain ⟨C₂, hC₂, h2⟩ := exists_nativeHalfEnd_uniform_completion_bound hκ0 hκ1 (M := 15/4) (by norm_num)
  refine ⟨e, χ, U, K*(C₁*C₂+8), hae, haU, hU, hUc, hUW.trans (subset_closure.trans hWs),
    het, he, hei, hflat, fun x hx => hone x (hUW (subset_closure hx)), hface, hχ, hc, hs, by finiteness, ?_⟩
  intro v hv hvb hODE τ V₀ hVeq hV₀ hVnonneg hVs f
  have hQ : ContDiffOn ℝ ∞ (nativeHalfEndPotentialCoefficient V₀) e.target :=
    (nativeHalfEndPotentialCoefficient_contDiffOn V₀ hVs).mono (fun x hx => by
      have hn : (3/4 : ℝ) < ‖x‖ := (het hx).1
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hx0
      simp only [hx0, norm_zero] at hn
      norm_num at hn)
  have hVM : ‖V₀‖ ≤ 15/4 := by
    apply (BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 15/4)).mpr
    intro t
    rw [Real.norm_of_nonneg (hVnonneg t),hVeq]
    have hp := pow_le_one₀ (hvb (t+τ)).1 (hvb (t+τ)).2.1 (n := 4)
    linarith
  have hco : nativeHalfEndPotentialCoefficient V₀ = fun x => -annularDelaunayPotential v τ x := by
    funext x
    simp only [nativeHalfEndPotentialCoefficient,hVeq,annularDelaunayPotential]
    have ht : -Real.log ‖x‖+τ = τ-Real.log ‖x‖ := by ring
    rw [ht]
    ring
  have hj : ∀ n ≤ 2, ∀ x ∈ W, ‖iteratedFDeriv ℝ n
      (fun y => (RiemannianMetric.euclideanMetric 3).pullbackVolumeDensity e y *
        nativeHalfEndPotentialCoefficient V₀ (e y)) x‖ ≤ M := by
    intro n hn x hx
    rw [hco]
    exact hMj v hv hvb hODE τ n hn x (subset_closure hx)
  let z := nativeHalfEndH2SourceCompletion hκ0 hκ1 V₀ hV₀ hVnonneg hVs f
  have hf := halfEndH2SourceGraph_entrance_H2_bound f.1
  have hr := hb _ hQ hj z (halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1))
    (nativeHalfEndH2SourceCompletionRHS hκ0 hκ1 V₀ hV₀ hVnonneg hVs f) hf.1
    (nativeHalfEndH2SourceCompletion_source hκ0 hκ1 V₀ hV₀ hVnonneg hVs f)
    (nativeHalfEndH2SourceCompletion_weak_equation hκ0 hκ1 V₀ hV₀ hVnonneg hVs f)
  refine ⟨hr.1, hr.2.trans ?_⟩
  calc
    _ ≤ K * (C₁ * (C₂ * ENNReal.ofReal ‖f.1‖) + 8 * ENNReal.ofReal ‖f.1‖) :=
      mul_le_mul le_rfl (add_le_add
        ((h1 z).trans (mul_le_mul le_rfl (h2 V₀ hVM hV₀ hVnonneg hVs f) zero_le zero_le)) hf.2) zero_le zero_le
    _ = _ := by ring

#print axioms exists_uniform_delaunay_entrance_chart_H4_witness
end Yamabe3.Analysis.UniformElliptic
