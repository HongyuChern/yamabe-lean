import Yamabe3.Analysis.UniformElliptic.NativeDelaunayPotentialError

/-!
# The full native Delaunay linear error is small from local H4 to H2

The operator is the actual negative-divergence principal expression minus
its actual rescaled native Jacobian potential. Its difference from the
flat Delaunay operator contains the genuine second-order metric error and
the genuine scalar/density potential error. The estimate applies to the
same function smooth only near the closure of a punctured annular domain.
It is uniform before the radius, finite chart, orbit, phase, domain and
function. No inverse or completed weighted space is assumed or concluded.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal BigOperators

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT Delaunay
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def nativeRescaledDelaunayJacobian (g : RiemannianMetric 3 E3)
    (r : ℝ) (v : ℝ → ℝ) (τ : ℝ) (w : E3 → ℝ) (z : E3) : ℝ :=
  principalSource (fun y => nativeDivergenceMatrix g (r • y)) w z -
    rescaledNativeJacobianPotential g r (delaunayRescaledBackground v r τ) z * w z

def flatDelaunayJacobian (v : ℝ → ℝ) (τ : ℝ) (w : E3 → ℝ) (z : E3) : ℝ :=
  principalSource (fun _ => 1) w z + annularDelaunayPotential v τ z * w z

def nativeDelaunayOperatorError (g : RiemannianMetric 3 E3)
    (r : ℝ) (v : ℝ → ℝ) (τ : ℝ) (w : E3 → ℝ) (z : E3) : ℝ :=
  -nativeScaledGeometricError g r w z + nativeDelaunayPotentialError g r v τ z * w z

/-- Linearity here is proved for the literal negative-divergence source,
including the derivatives of its coefficient field. -/
theorem principalSource_sub_coefficients
    (a b : E3 → Matrix (Fin 3) (Fin 3) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun z => a z i j))
    (hb : ∀ i j, ContDiff ℝ ∞ (fun z => b z i j))
    {w : E3 → ℝ} (hw : ContDiff ℝ ∞ w) (z : E3) :
    principalSource (fun y => a y - b y) w z =
      principalSource a w z - principalSource b w z := by
  let F := matrixFlux a (fun j => partialDeriv j w)
  let G := matrixFlux b (fun j => partialDeriv j w)
  have hF (i : Fin 3) : ContDiff ℝ ∞ (F i) :=
    ContDiff.sum fun j _ => (ha i j).mul (contDiff_partial hw j)
  have hG (i : Fin 3) : ContDiff ℝ ∞ (G i) :=
    ContDiff.sum fun j _ => (hb i j).mul (contDiff_partial hw j)
  have hflux (i : Fin 3) :
      matrixFlux (fun y => a y - b y) (fun j => partialDeriv j w) i =
        fun y => F i y - G i y := by
    funext y
    simp only [matrixFlux, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, F, G]
  have hpartial (i : Fin 3) :
      partialDeriv i (fun y => F i y - G i y) z = partialDeriv i (F i) z - partialDeriv i (G i) z := by
    unfold partialDeriv
    rw [fderiv_fun_sub ((hF i).differentiable (by simp) z)
      ((hG i).differentiable (by simp) z)]
    simp only [sub_apply]
  simp only [principalSource, hflux, hpartial, Finset.sum_sub_distrib]
  change -((∑ i : Fin 3, partialDeriv i (F i) z) - ∑ i : Fin 3, partialDeriv i (G i) z) = _
  ring

/-- The error is exactly the difference of the two displayed actual
operators at this same point and on this same function. -/
theorem nativeDelaunayOperatorError_eq_operator_difference
    (g : RiemannianMetric 3 E3) {r : ℝ} (hr : 0 < r)
    (v : ℝ → ℝ) (τ : ℝ) {O : Set E3} (hO : IsOpen O)
    {w : E3 → ℝ} (hw : ContDiffOn ℝ ∞ w O) {z : E3}
    (hzO : z ∈ O) (hz : z ≠ 0) :
    nativeDelaunayOperatorError g r v τ w z =
      nativeRescaledDelaunayJacobian g r v τ w z - flatDelaunayJacobian v τ w z := by
  obtain ⟨W, hW, _, hWw⟩ := exists_smooth_compact_extension_near_compact
    hO (isCompact_singleton (x := z)) (singleton_subset_iff.mpr hzO) hw
  have hg := hWw z (mem_singleton z)
  have hs := principalSource_sub_coefficients
    (fun y => nativeDivergenceMatrix g (r • y)) (fun _ => 1)
    (fun i j => (contDiff_nativeDivergenceMatrix g i j).comp (contDiff_id.const_smul r))
    (fun _ _ => contDiff_const) hW z
  rw [principalSource_eq_of_eventuallyEq _ hg,
    principalSource_eq_of_eventuallyEq _ hg,
    principalSource_eq_of_eventuallyEq _ hg] at hs
  rw [nativeDelaunayOperatorError,
    nativeScaledGeometricError_eq_negative_principalSource_locally g r hO hw hzO,
    hs, neg_neg, nativeRescaledDelaunayJacobian,
    rescaledNativeJacobianPotential_delaunay g hr v τ hz, flatDelaunayJacobian]
  ring

/-- This algebraic identity fixes all first- and second-order signs. -/
theorem nativeDelaunayOperatorError_eq_secondOrderPerturbation
    (g : RiemannianMetric 3 E3) (r : ℝ) (v : ℝ → ℝ) (τ : ℝ)
    (w : E3 → ℝ) :
    nativeDelaunayOperatorError g r v τ w =
      secondOrderPerturbation (fun i j z => -nativeScaledPrincipalError g r i j z)
        (fun i z => -nativeScaledFirstError g r i z)
        (nativeDelaunayPotentialError g r v τ) w := by
  funext z
  simp only [nativeDelaunayOperatorError, nativeScaledGeometricError,
    secondOrderPerturbation, zero_mul, add_zero, neg_mul, Finset.sum_neg_distrib]
  ring

/-- This is a small bound on the full genuine differential error, measured
in the actual derivative profiles on the same domain. All coefficient,
scalar-curvature and orbit estimates precede the function being solved for. -/
theorem exists_uniform_local_small_native_delaunay_operator_error
    {ι : Type*} (Λ : Finset ι) (gE : ι → RiemannianMetric 3 E3)
    (hB : ∀ p ∈ Λ, (gE p).euclideanCoefficients 0 = innerSL ℝ)
    (hρ : ∀ p ∈ Λ, (gE p).pullbackVolumeDensity id 0 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ → ∀ p ∈ Λ,
      ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
        (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1 / 2) →
        (∀ t, deriv (deriv v) t = radialForce (v t)) →
        ∀ (τ : ℝ) (O Ω : Set E3), IsOpen O → IsOpen Ω →
          IsCompact (closure Ω) → closure Ω ⊆ O → (∀ z ∈ O, z ≠ 0) →
          (∀ z ∈ Ω, (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 2) →
          ∀ w : E3 → ℝ, ContDiffOn ℝ ∞ w O →
            derivativeProfile 2 Ω 2 (nativeDelaunayOperatorError (gE p) r v τ w) ≤
              ENNReal.ofReal ε * derivativeProfile 2 Ω 4 w := by
  let η : ℝ := ε / 91
  have hη : 0 < η := div_pos hε (by norm_num)
  obtain ⟨d₁, hd₁, hprincipal⟩ := exists_uniform_small_native_geometric_error
    Λ gE hB hρ (by norm_num : (0 : ℝ) < 2) hε
  obtain ⟨d₂, hd₂, hpotential⟩ := exists_uniform_small_finite_native_delaunay_potential_error
    Λ gE hρ 2 hη
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, ?_⟩
  intro r hr hrd p hp v hv hvb hODE τ O Ω hO hΩ hΩc hΩO hO0 hΩann w hw
  have hr₁ : r < d₁ := hrd.trans_le (min_le_left _ _)
  have hr₂ : r < d₂ := hrd.trans_le (min_le_right _ _)
  have hAB := hprincipal r hr hr₁ p hp
  let c := nativeDelaunayPotentialError (gE p) r v τ
  have hc : ContDiffOn ℝ ∞ c O := fun z hz =>
    (contDiffAt_nativeDelaunayPotentialError (gE p) r hv τ (hO0 z hz)).contDiffWithinAt
  obtain ⟨C, hC, _, hCc⟩ := exists_smooth_compact_extension_near_compact hO hΩc hΩO hc
  obtain ⟨W, hW, _, hWw⟩ := exists_smooth_compact_extension_near_compact hO hΩc hΩO hw
  have hΩball {z : E3} (hz : z ∈ Ω) : z ∈ closedBall (0 : E3) 2 := by
    simpa only [mem_closedBall, dist_zero_right] using (hΩann z hz).2
  have hCjet (n : ℕ) (hn : n ≤ 2) (z : E3) (hz : z ∈ Ω) :
      ‖iteratedFDeriv ℝ n C z‖ ≤ η := by
    rw [((hCc z (subset_closure hz)).iteratedFDeriv ℝ n).self_of_nhds]
    exact hpotential r hr hr₂ p hp v hv hvb hODE τ n hn z
      (hΩann z hz).1 (hΩann z hz).2
  have hbound := derivativeProfile_two_secondOrderPerturbation_le hΩ hη.le
    (fun i j z => -nativeScaledPrincipalError (gE p) r i j z)
    (fun i z => -nativeScaledFirstError (gE p) r i z) C W
    (fun i j => (contDiff_nativeScaledPrincipalError (gE p) r i j).neg)
    (fun i => (contDiff_nativeScaledFirstError (gE p) r i).neg) hC hW
    (fun n hn z hz i j => by
      change ‖iteratedFDeriv ℝ n (-nativeScaledPrincipalError (gE p) r i j) z‖ ≤ η
      rw [iteratedFDeriv_neg_apply, norm_neg]
      exact hAB.1 n hn z (hΩball hz) i j)
    (fun n hn z hz i => by
      change ‖iteratedFDeriv ℝ n (-nativeScaledFirstError (gE p) r i) z‖ ≤ η
      rw [iteratedFDeriv_neg_apply, norm_neg]
      exact hAB.2.1 n hn z (hΩball hz) i)
    hCjet
  have heq (z : E3) (hz : z ∈ Ω) :
      secondOrderPerturbation
          (fun i j y => -nativeScaledPrincipalError (gE p) r i j y)
          (fun i y => -nativeScaledFirstError (gE p) r i y) C W =ᶠ[𝓝 z]
        nativeDelaunayOperatorError (gE p) r v τ w := by
    have hcg := hCc z (subset_closure hz)
    have hwg := hWw z (subset_closure hz)
    have heg := nativeScaledGeometricError_eventuallyEq (gE p) r hwg
    filter_upwards [hcg, hwg, heg] with y hcy hwy hey
    change secondOrderPerturbation _ _ C W y = -nativeScaledGeometricError (gE p) r w y + c y * w y
    rw [← hcy, ← hwy, ← hey]
    simp only [nativeScaledGeometricError, secondOrderPerturbation, zero_mul,
      add_zero, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [derivativeProfile_eq_of_local_germs hΩ.measurableSet heq 2 2,
    derivativeProfile_eq_of_local_germs hΩ.measurableSet
      (fun z hz => hWw z (subset_closure hz)) 2 4] at hbound
  simpa only [show 91 * η = ε by dsimp only [η]; ring] using hbound

#print axioms principalSource_sub_coefficients
#print axioms nativeDelaunayOperatorError_eq_operator_difference
#print axioms nativeDelaunayOperatorError_eq_secondOrderPerturbation
#print axioms exists_uniform_local_small_native_delaunay_operator_error

end Yamabe3.Analysis.UniformElliptic
