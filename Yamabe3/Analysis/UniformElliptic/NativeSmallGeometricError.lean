import Yamabe3.Analysis.UniformElliptic.SmallDilatedJets
import Yamabe3.Analysis.UniformElliptic.SecondOrderPerturbationProfile

/-!
# The actual rescaled native principal error is small from H4 to H2

The coefficient is the genuine density-weighted inverse metric of the
supplied native coordinate metric, minus its identity value at the pole.
Its first-order coefficient is its actual divergence. Finite jets through
order three become uniformly small under dilation, before the scale,
finite pole, domain and test function are quantified.

The differential error is exactly minus the native divergence-form source
of that coefficient difference. The proved two-derivative estimate then
gives an arbitrarily small H4-to-H2 bound. This treats the principal
geometric error; scalar-curvature and nonlinear potential differences
must still be estimated in their own actual source norms.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal BigOperators

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.Euclidean

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def nativeScaledPrincipalError (g : RiemannianMetric 3 E3) (r : ℝ)
    (i j : Fin 3) (z : E3) : ℝ :=
  nativeDivergenceMatrix g (r • z) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j

def nativeScaledFirstError (g : RiemannianMetric 3 E3) (r : ℝ)
    (j : Fin 3) (z : E3) : ℝ :=
  ∑ i : Fin 3, partialDeriv i (nativeScaledPrincipalError g r i j) z

def nativeScaledGeometricError (g : RiemannianMetric 3 E3) (r : ℝ)
    (v : E3 → ℝ) : E3 → ℝ :=
  secondOrderPerturbation (nativeScaledPrincipalError g r)
    (nativeScaledFirstError g r) (fun _ => 0) v

theorem contDiff_nativeScaledPrincipalError (g : RiemannianMetric 3 E3)
    (r : ℝ) (i j : Fin 3) : ContDiff ℝ ∞ (nativeScaledPrincipalError g r i j) :=
  ((contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r)).sub contDiff_const

theorem contDiff_nativeScaledFirstError (g : RiemannianMetric 3 E3)
    (r : ℝ) (j : Fin 3) : ContDiff ℝ ∞ (nativeScaledFirstError g r j) :=
  ContDiff.sum fun i _ => contDiff_partial (contDiff_nativeScaledPrincipalError g r i j) i

/-- The actual first-order term is exactly the divergence of the same
actual principal coefficient difference, with the negative-source sign. -/
theorem nativeScaledGeometricError_eq_negative_principalSource
    (g : RiemannianMetric 3 E3) (r : ℝ) {v : E3 → ℝ}
    (hv : ContDiff ℝ ∞ v) (x : E3) :
    nativeScaledGeometricError g r v x =
      -principalSource (fun z => nativeDivergenceMatrix g (r • z) - 1) v x := by
  let a : E3 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun z => nativeDivergenceMatrix g (r • z) - 1
  have ha : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun z => a z i j) :=
    contDiff_nativeScaledPrincipalError g r
  change secondOrderPerturbation (fun i j z => a z i j)
    (fun j z => ∑ i : Fin 3, partialDeriv i (fun y => a y i j) z)
    (fun _ => 0) v x = -principalSource a v x
  rw [principalSource_eq_secondOrderOperator (fun _ _ => 0) ha hv]
  simp only [secondOrderPerturbation, secondOrderOperator, zero_mul,
    Finset.sum_const_zero, add_zero, zero_sub, neg_mul, Finset.sum_neg_distrib]
  ring

theorem exists_uniform_small_native_geometric_error
    {ι : Type*} (Λ : Finset ι) (gE : ι → RiemannianMetric 3 E3)
    (hB : ∀ p ∈ Λ, (gE p).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ p ∈ Λ, (gE p).pullbackVolumeDensity id 0 = 1)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ → ∀ p ∈ Λ,
      (∀ n ≤ 2, ∀ z ∈ closedBall (0 : E3) R, ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ n (nativeScaledPrincipalError (gE p) r i j) z‖ ≤ τ / 91) ∧
      (∀ n ≤ 2, ∀ z ∈ closedBall (0 : E3) R, ∀ j : Fin 3,
        ‖iteratedFDeriv ℝ n (nativeScaledFirstError (gE p) r j) z‖ ≤ τ / 91) ∧
      ∀ Ω : Set E3, IsOpen Ω → Ω ⊆ closedBall (0 : E3) R →
        ∀ v : E3 → ℝ, ContDiff ℝ ∞ v →
        derivativeProfile 2 Ω 2 (nativeScaledGeometricError (gE p) r v) ≤
          ENNReal.ofReal τ * derivativeProfile 2 Ω 4 v := by
  classical
  let η : ℝ := τ / 91
  have hη : 0 < η := div_pos hτ (by norm_num)
  let f : (Λ × Fin 3 × Fin 3) → E3 → ℝ := fun q x =>
    nativeDivergenceMatrix (gE q.1) x q.2.1 q.2.2 -
      (1 : Matrix (Fin 3) (Fin 3) ℝ) q.2.1 q.2.2
  have hf (q : Λ × Fin 3 × Fin 3) : ContDiff ℝ ∞ (f q) :=
    (contDiff_nativeDivergenceMatrix (gE q.1) q.2.1 q.2.2).sub contDiff_const
  have hzero (q : Λ × Fin 3 × Fin 3) : f q 0 = 0 := by
    dsimp only [f]
    rw [nativeDivergenceMatrix_zero (gE q.1) (hB q.1 q.1.property) (hρ q.1 q.1.property)]
    exact sub_self _
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_finite_rescaled_zero_jets f hf hzero 3 hR
    (div_pos hη (by norm_num : (0 : ℝ) < 3))
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ p hp
  have hA3 (n : ℕ) (hn : n ≤ 3) (z : E3) (hz : z ∈ closedBall (0 : E3) R)
      (i j : Fin 3) :
      ‖iteratedFDeriv ℝ n (nativeScaledPrincipalError (gE p) r i j) z‖ ≤ η / 3 :=
    hsmall r hr hrδ (⟨p, hp⟩, i, j) n hn z hz
  have hA (n : ℕ) (hn : n ≤ 2) (z : E3) (hz : z ∈ closedBall (0 : E3) R)
      (i j : Fin 3) :
      ‖iteratedFDeriv ℝ n (nativeScaledPrincipalError (gE p) r i j) z‖ ≤ η :=
    (hA3 n (by omega) z hz i j).trans (by linarith [hη])
  have hb (n : ℕ) (hn : n ≤ 2) (z : E3) (hz : z ∈ closedBall (0 : E3) R)
      (j : Fin 3) :
      ‖iteratedFDeriv ℝ n (nativeScaledFirstError (gE p) r j) z‖ ≤ η := by
    unfold nativeScaledFirstError
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      (contDiff_partial (contDiff_nativeScaledPrincipalError (gE p) r i j) i).contDiffAt.of_le
        (by exact_mod_cast le_top))]
    apply (norm_sum_le _ _).trans
    calc
      (∑ i : Fin 3, ‖iteratedFDeriv ℝ n
          (partialDeriv i (nativeScaledPrincipalError (gE p) r i j)) z‖) ≤
          ∑ _i : Fin 3, η / 3 := by
        apply Finset.sum_le_sum
        intro i _
        exact (norm_iteratedFDeriv_partial_le
          (contDiff_nativeScaledPrincipalError (gE p) r i j) i n z).trans
            (hA3 (n + 1) (by omega) z hz i j)
      _ = η := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  refine ⟨hA, hb, ?_⟩
  intro Ω hΩ hΩR v hv
  have hbnd := derivativeProfile_two_secondOrderPerturbation_le hΩ hη.le
    (nativeScaledPrincipalError (gE p) r) (nativeScaledFirstError (gE p) r) (fun _ => 0) v
    (contDiff_nativeScaledPrincipalError (gE p) r)
    (contDiff_nativeScaledFirstError (gE p) r) contDiff_const hv
    (fun n hn z hz i j => hA n hn z (hΩR hz) i j)
    (fun n hn z hz j => hb n hn z (hΩR hz) j)
    (fun n _ z _ => by simp; exact hη.le)
  have hnum : 91 * η = τ := by dsimp only [η]; ring
  simpa only [nativeScaledGeometricError, hnum] using hbnd

#print axioms nativeScaledGeometricError_eq_negative_principalSource
#print axioms exists_uniform_small_native_geometric_error

end Yamabe3.Analysis.UniformElliptic
