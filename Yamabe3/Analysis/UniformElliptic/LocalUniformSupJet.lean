import Yamabe3.Analysis.UniformElliptic.LocalUniformJet
import Yamabe3.Analysis.UniformElliptic.UniformProfileBound

/-!
# Local uniform jet estimates in pointwise input norms

The genuine derivative profiles are bounded by the actual finite volume of
the fixed region. This corollary keeps the estimate homogeneous in the value
bound and source-jet bound; these may tend to zero with the geometric scale.
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

theorem exists_local_uniform_sup_jet_bound
    (m : ℕ) {Ω O V K : Set E} (hO : IsOpen O)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hVΩ : closure V ⊆ Ω) (hK : IsCompact K) (hKV : K ⊆ V)
    {κ L Q : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : SmoothEllipticBilinearForm d Ω), κ ≤ B.lam →
      (∀ n ≤ m + 1 + d, ∀ x ∈ V, ∀ i j : Fin d,
        ‖iteratedFDeriv ℝ n (fun y => B.a y i j) x‖ ≤ L) →
      (∀ x ∈ V, (∑ i : Fin d, ∑ j : Fin d,
        (B.a x i j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) ^ 2) ≤ 1 / 4) →
      ∀ (q : E → ℝ), ContDiff ℝ ∞ q →
      (∀ n ≤ m + d - 1, ∀ x ∈ V, ‖iteratedFDeriv ℝ n q x‖ ≤ Q) →
      ∀ {u f : E → ℝ}, ContDiffOn ℝ ∞ u O → ContDiffOn ℝ ∞ f O →
        WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u))
          (fun x => f x + q x * u x) →
        ∀ A H : ℝ, 0 ≤ A → 0 ≤ H →
          (∀ x ∈ V, ‖u x‖ ≤ A) →
          (∀ n ≤ m + d - 1, ∀ x ∈ V, ‖iteratedFDeriv ℝ n f x‖ ≤ H) →
          ∀ x ∈ K, ‖iteratedFDeriv ℝ m u x‖ ≤ C * (A + H) := by
  obtain ⟨C, hC, hb⟩ := exists_local_uniform_pointwise_jet_bound
    m hO hV hVc hVO hVΩ hK hKV hκ hL hQ
  let k := m + d - 1
  let v : ℝ := (volume V).toReal ^ (1 / 2 : ℝ)
  have hv : 0 ≤ v := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hk : (1 : ℝ) ≤ k + 1 := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hfinite : volume V ≠ ⊤ :=
    ne_of_lt ((measure_mono subset_closure).trans_lt hVc.measure_lt_top)
  refine ⟨C * ((k + 1 : ℝ) * v), mul_nonneg hC (mul_nonneg (by positivity) hv), ?_⟩
  intro B hB hjet hosc q hq hqjet u f hu hf heq A H hA hH huB hfB x hx
  have hu0 : ∀ n ≤ 0, ∀ y ∈ V, ‖iteratedFDeriv ℝ n u y‖ ≤ A := by
    intro n hn y hy
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    simpa only [norm_iteratedFDeriv_zero] using huB y hy
  have hut := derivativeProfile_ne_top_of_jet_bound hV.measurableSet hfinite 0 hA hu0
  have hft := derivativeProfile_ne_top_of_jet_bound hV.measurableSet hfinite k hH hfB
  have hup := derivativeProfile_toReal_le_of_jet_bound hV.measurableSet hfinite 0 hA hu0
  have hfp := derivativeProfile_toReal_le_of_jet_bound hV.measurableSet hfinite k hH hfB
  have hprofile : (derivativeProfile 2 V 0 u + derivativeProfile 2 V k f).toReal ≤
      ((k + 1 : ℝ) * v) * (A + H) := by
    rw [ENNReal.toReal_add hut hft]
    have hau : A * v ≤ ((k + 1 : ℝ) * v) * A := by
      have h := mul_le_mul_of_nonneg_right hk (mul_nonneg hA hv)
      nlinarith [h]
    calc
      _ ≤ A * v + (k + 1 : ℝ) * H * v := by
        exact add_le_add (by simpa only [Nat.cast_zero, zero_add, one_mul] using hup) hfp
      _ ≤ ((k + 1 : ℝ) * v) * A + (k + 1 : ℝ) * H * v :=
        add_le_add hau le_rfl
      _ = _ := by ring
  exact (hb B hB hjet hosc q hq hqjet hu hf heq x hx).trans (by
    calc
      _ ≤ C * (((k + 1 : ℝ) * v) * (A + H)) := mul_le_mul_of_nonneg_left hprofile hC
      _ = _ := by ring)

#print axioms exists_local_uniform_sup_jet_bound

end Yamabe3.Analysis.UniformElliptic
