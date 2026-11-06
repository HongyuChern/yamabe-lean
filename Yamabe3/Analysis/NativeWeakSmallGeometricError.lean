import Yamabe3.Analysis.WeakGeometricPerturbation

/-! Smallness of the genuine native principal error on actual weak H4
inputs. The coefficient jets are produced from the normalized metric.
Uniformity precedes scale, pole, precompact domain and weak input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ENNReal Topology ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)

def nativeWeakScaledGeometricError (g : RiemannianMetric 3 E) (r : ℝ)
    (O : Set E) (u : E → ℝ) : E → ℝ :=
  weakSecondOrderPerturbation O (nativeScaledPrincipalError g r)
    (nativeScaledFirstError g r) (fun _ => 0) u

theorem exists_uniform_weak_small_native_geometric_error
    {ι : Type*} (Λ : Finset ι) (gE : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ, (gE p).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ p ∈ Λ, (gE p).pullbackVolumeDensity id 0 = 1)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ → ∀ p ∈ Λ,
      ∀ O : Set E, IsOpen O → IsCompact (closure O) → O ⊆ closedBall (0:E) R →
      ∀ u : E → ℝ, MemWkp 4 2 u O →
        MemWkp 2 2 (nativeWeakScaledGeometricError (gE p) r O u) O ∧
        iteratedWeakSobolevNorm 2 2 (nativeWeakScaledGeometricError (gE p) r O u) O ≤
          ENNReal.ofReal τ * iteratedWeakSobolevNorm 4 2 u O := by
  have hsmall : 0 < τ/7 := div_pos hτ (by norm_num)
  obtain ⟨δ,hδ,hjets⟩ := exists_uniform_small_native_geometric_error Λ gE hB hρ hR hsmall
  refine ⟨δ,hδ,?_⟩
  intro r hr hrδ p hp O hO hOc hOR u hu
  have hj := hjets r hr hrδ p hp
  have hη : 0 ≤ τ/637 := div_nonneg hτ.le (by norm_num)
  have hab : τ/7/91 = τ/637 := by ring
  have hA : ∀ n ≤ 2, ∀ x ∈ O, ∀ i j, ‖iteratedFDeriv ℝ n (nativeScaledPrincipalError (gE p) r i j) x‖ ≤ τ/637 := by
    intro n hn x hx i j
    simpa only [hab] using hj.1 n hn x (hOR hx) i j
  have hB' : ∀ n ≤ 2, ∀ x ∈ O, ∀ j, ‖iteratedFDeriv ℝ n (nativeScaledFirstError (gE p) r j) x‖ ≤ τ/637 := by
    intro n hn x hx j
    simpa only [hab] using hj.2.1 n hn x (hOR hx) j
  have hZ : ∀ n ≤ 2, ∀ x ∈ O, ‖iteratedFDeriv ℝ n (fun _ : E => (0:ℝ)) x‖ ≤ τ/637 := by
    intro n hn x hx
    simpa using hη
  have hh := weakSecondOrderPerturbation_mem_bound hO hOc hη
    (nativeScaledPrincipalError (gE p) r) (nativeScaledFirstError (gE p) r) (fun _ => 0) u
    (contDiff_nativeScaledPrincipalError (gE p) r) (contDiff_nativeScaledFirstError (gE p) r)
    contDiff_const hu hA hB' hZ
  simpa only [nativeWeakScaledGeometricError,show (637:ℝ)*(τ/637)=τ by ring] using hh

#print axioms exists_uniform_weak_small_native_geometric_error
end Yamabe3.Analysis.UniformElliptic
