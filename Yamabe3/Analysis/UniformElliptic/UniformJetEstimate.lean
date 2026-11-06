import Yamabe3.Analysis.UniformElliptic.UniformZerothOrder
import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Embedding.Compact

/-!
# Genuine uniform pointwise jets for variable-potential equations

The quantitative Sobolev embedding constant depends only on the fixed
compact set and neighborhoods. It is combined with the proved coefficient-
family uniform higher-order estimate. In dimension three, second derivatives
use the existing H6 embedding and fourth source derivatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A uniform native Euclidean jet estimate for the actual weak equation,
with common coefficient and signed potential bounds. All constants precede
B, q, u, f and the evaluation point. -/
theorem exists_uniform_pointwise_jet_bound
    (m : ℕ) {Ω V K : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) (hK : IsCompact K) (hKV : K ⊆ V)
    {κ L Q : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ n ≤ m + 1 + d, ∀ x ∈ V, ∀ i j : Fin d,
        ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ (q : E → ℝ), ContDiff ℝ ∞ q →
      (∀ n ≤ m + d - 1, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q x‖ ≤ Q) →
      ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u))
          (fun x => f x + q x * u x) →
        ∀ x ∈ K, ‖iteratedFDeriv ℝ m u x‖ ≤ C *
          (derivativeProfile 2 V 0 u + derivativeProfile 2 V (m + d - 1) f).toReal := by
  obtain ⟨W, hW, hKW, hWV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  have hWc : IsCompact (closure W) :=
    hVc.of_isClosed_subset isClosed_closure (hWV.trans subset_closure)
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hk : m + d - 1 + 2 = m + 1 + d := by omega
  obtain ⟨H, hH, hbound⟩ := exists_uniform_derivativeProfile_add_two_with_potential
    (m + d - 1) hV hVc hVΩ hW hWc hWV hκ hL hQ
  obtain ⟨A, hA, hembed⟩ := smooth_jet_le_l2_derivativeProfile_on_compact hK hW hWc hKW m
  refine ⟨A * H, mul_nonneg hA.le hH, ?_⟩
  intro B hB hjet hosc q hq hqjet u f hu hf heq x hx
  have hjet' : ∀ n ≤ m + d - 1 + 2, ∀ x ∈ V, ∀ i j : Fin d,
      ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L := by
    simpa only [hk] using hjet
  have h := hbound B hB hjet' hosc q hq hqjet hu hf heq
  rw [hk] at h
  have hfinite : ENNReal.ofReal H *
      (derivativeProfile 2 V 0 u + derivativeProfile 2 V (m + d - 1) f) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨derivativeProfile_ne_top_on_precompact hVc 0 hu,
        derivativeProfile_ne_top_on_precompact hVc (m + d - 1) hf⟩)
  have hreal := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hH] at hreal
  exact (hembed hu x hx).trans (by
    calc
      _ ≤ A * (H * (derivativeProfile 2 V 0 u +
          derivativeProfile 2 V (m + d - 1) f).toReal) :=
        mul_le_mul_of_nonneg_left hreal hA.le
      _ = _ := by ring)

#print axioms exists_uniform_pointwise_jet_bound

end Yamabe3.Analysis.UniformElliptic
