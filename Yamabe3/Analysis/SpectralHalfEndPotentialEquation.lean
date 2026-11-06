import Yamabe3.Analysis.SpectralHalfEndPotentialEntrance
import Yamabe3.Analysis.HalfEndScalarForcedEquation
import Yamabe3.Analysis.HalfEndC2Regularity

/-!
# Actual coordinate equations of the same potential Poisson curve

The half-end curve is the already constructed
`spectralHalfPotentialPoissonCLM`, with its actual reciprocal entrance
vector.  On positive times its free term is the literal exponential
Poisson coordinate, and its correction is the same full-line canonical
potential inverse applied to the actual potential times that free term.

The true coordinate equation of that canonical inverse therefore gives
the positive-time homogeneous equation of the original half-end curve.
The equation and continuity of the bounded continuous potential produce
C2 regularity of every actual coordinate.  No C1 datum, free equation,
smooth source, or different representative is an input.  All regularity
statements are restricted to `Ioi 0`; no derivative across the entrance
of the even full-line Poisson extension is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff lp BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

variable {ι : Type*} (k : ι → ℝ) {k₀ κ : ℝ}
  (hk₀ : 2 < k₀) (hk : ∀ i, k₀ ≤ k i) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
  (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant k₀ (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- A literal zero coordinate of the entrance datum remains zero in the
same potential Poisson curve, including the entrance time. -/
theorem spectralHalfPotentialPoissonCLM_coordinate_zero
    (b : SpectralSpace ι) (i : ι) (hb : b i = 0) (t : ℝ≥0) :
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b t i = 0 := by
  let a := spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 b
  have ha : a i = 0 := by
    dsimp only [a]
    rw [spectralHalfEntranceInverseCLM_coordinate, hb, mul_zero]
  have hQ (s : ℝ) : spectralFullBoundaryPoissonCLM k hk₀ hk a s i = 0 := by
    rw [spectralFullBoundaryPoissonCLM_coordinate, ha, mul_zero]
  have hC (s : ℝ) :
      spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV a s i = 0 := by
    rw [spectralHalfFullPotentialCorrectionCLM_apply]
    apply spectralIntegralPotentialInverse_coordinate_zero k
      (by linarith : 0 < k₀) hk
      (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀)
      hκ0 hκ1 V hV (V • spectralFullBoundaryPoissonCLM k hk₀ hk a) i
    intro r
    change V r * spectralFullBoundaryPoissonCLM k hk₀ hk a r i = 0
    rw [hQ r, mul_zero]
  rw [spectralHalfPotentialPoissonCLM_apply]
  change spectralFullBoundaryPoissonCLM k hk₀ hk a (t : ℝ) i -
    spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV a (t : ℝ) i = 0
  rw [hQ (t : ℝ), hC (t : ℝ), sub_self]

/-- The actual first and second coordinate derivatives of the original
same-potential Poisson curve on positive times.  The potential enters
with the literal minus sign in the second-order scalar equation. -/
theorem spectralHalfPotentialPoissonCLM_coordinate_equation
    (b : SpectralSpace ι) (i : ι) (t : ℝ) (ht : 0 < t) :
    let y := fun s : ℝ =>
      spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b s.toNNReal i
    DifferentiableAt ℝ y t ∧
      HasDerivAt (deriv y) (4 * deriv y t + (k i ^ 2 - 4 - V t) * y t) t := by
  dsimp only
  let a := spectralHalfEntranceInverseCLM k hk₀ hk hκ0 hκ1 V hV hV0 b
  let Q := spectralFullBoundaryPoissonCLM k hk₀ hk a
  let C := spectralHalfFullPotentialCorrectionCLM k hk₀ hk hκ0 hκ1 V hV a
  let q : ℝ → ℝ := fun s => Real.exp ((2 - k i) * s) * a i
  let U : ℝ → ℝ := fun s => q s - C s i
  let y : ℝ → ℝ := fun s =>
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b s.toNNReal i
  have hC := spectralIntegralPotentialInverse_coordinate_equation k
    (by linarith : 0 < k₀) hk
    (by norm_num; exact hk₀ : |(-2 : ℝ)| < k₀)
    hκ0 hκ1 V hV (V • Q) i
  change Differentiable ℝ (fun s => C s i) ∧
    Differentiable ℝ (deriv (fun s => C s i)) ∧
    (∀ s, deriv (deriv (fun r => C r i)) s =
      -2 * (-2) * deriv (fun r => C r i) s +
        (k i ^ 2 - (-2) ^ 2) * C s i + (V • Q) s i - V s * C s i) at hC
  have hCeq (s : ℝ) : deriv (deriv (fun r => C r i)) s =
      4 * deriv (fun r => C r i) s +
        (k i ^ 2 - 4) * C s i + V s * Q s i - V s * C s i := by
    have h := hC.2.2 s
    change deriv (deriv (fun r => C r i)) s =
      -2 * (-2) * deriv (fun r => C r i) s +
        (k i ^ 2 - (-2) ^ 2) * C s i + V s * Q s i - V s * C s i at h
    norm_num at h
    exact h
  have hq (s : ℝ) : HasDerivAt q ((2 - k i) * q s) s := by
    apply (((hasDerivAt_id s).const_mul (2 - k i)).exp.mul_const (a i)).congr_deriv
    dsimp only [q, id_eq]
    ring
  have hqD : deriv q = fun s => (2 - k i) * q s := funext fun s => (hq s).deriv
  have hqDiff : Differentiable ℝ q := fun s => (hq s).differentiableAt
  have hqDDiff : Differentiable ℝ (deriv q) := by
    rw [hqD]
    exact fun s => ((hq s).const_mul (2 - k i)).differentiableAt
  have hqDD (s : ℝ) : deriv (deriv q) s = (2 - k i) ^ 2 * q s := by
    rw [hqD, ((hq s).const_mul (2 - k i)).deriv]
    ring
  have hU : Differentiable ℝ U := hqDiff.sub hC.1
  have hUD : deriv U = fun s => deriv q s - deriv (fun r => C r i) s := by
    funext s
    exact deriv_sub (hqDiff s) (hC.1 s)
  have hUDDiff : Differentiable ℝ (deriv U) := by
    rw [hUD]
    exact hqDDiff.sub hC.2.1
  have hQ (s : ℝ) (hs : 0 < s) : Q s i = q s := by
    dsimp only [Q, q]
    rw [spectralFullBoundaryPoissonCLM_coordinate, abs_of_nonneg hs.le]
    congr 2
    ring
  have hUEquation : deriv (deriv U) t =
      4 * deriv U t + (k i ^ 2 - 4 - V t) * U t := by
    have hsub := ((hqDDiff t).hasDerivAt.sub (hC.2.1 t).hasDerivAt)
    change HasDerivAt (fun s => deriv q s - deriv (fun r => C r i) s)
      (deriv (deriv q) t - deriv (deriv (fun r => C r i)) t) t at hsub
    rw [hUD, hsub.deriv, hqDD t, hCeq t, hqD, hQ t ht]
    dsimp only [U]
    ring
  have heq : y =ᶠ[𝓝 t] U := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    dsimp only [y, U, q]
    rw [spectralHalfPotentialPoissonCLM_apply]
    change spectralFullBoundaryPoissonCLM k hk₀ hk a (s.toNNReal : ℝ) i -
      C (s.toNNReal : ℝ) i = _
    rw [spectralFullBoundaryPoissonCLM_coordinate, Real.coe_toNNReal s hs.le,
      abs_of_nonneg hs.le]
    rw [show 2 * s - k i * s = (2 - k i) * s by ring]
  change DifferentiableAt ℝ y t ∧
    HasDerivAt (deriv y) (4 * deriv y t + (k i ^ 2 - 4 - V t) * y t) t
  refine ⟨((hU t).hasDerivAt.congr_of_eventuallyEq heq).differentiableAt, ?_⟩
  apply ((hUDDiff t).hasDerivAt.congr_of_eventuallyEq heq.deriv).congr_deriv
  rw [hUEquation, heq.deriv_eq, heq.self_of_nhds]

/-- Continuity of the actual potential and the produced coordinate
equation give C2 regularity of that same weighted coordinate. -/
theorem spectralHalfPotentialPoissonCLM_coordinate_c2
    (b : SpectralSpace ι) (i : ι) :
    ContDiffOn ℝ 2 (fun s : ℝ =>
      spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b s.toNNReal i)
      (Ioi 0) := by
  let y : ℝ → ℝ := fun s =>
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b s.toNNReal i
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt y (deriv y t) t :=
    (spectralHalfPotentialPoissonCLM_coordinate_equation
      k hk₀ hk hκ0 hκ1 V hV hV0 b i t ht).1.hasDerivAt
  have hdd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (deriv y) (4 * deriv y t + (k i ^ 2 - 4 - V t) * y t) t :=
    (spectralHalfPotentialPoissonCLM_coordinate_equation
      k hk₀ hk hκ0 hκ1 V hV hV0 b i t ht).2
  have hy : ContinuousOn y (Ioi 0) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdy : ContinuousOn (deriv y) (Ioi 0) :=
    fun t ht => (hdd t ht).continuousAt.continuousWithinAt
  have hcoef : ContinuousOn (fun t : ℝ => k i ^ 2 - 4 - V t) (Ioi 0) :=
    continuousOn_const.sub V.continuous.continuousOn
  exact contDiffOn_two_of_continuous_second_derivative isOpen_Ioi y (deriv y)
    (fun t => 4 * deriv y t + (k i ^ 2 - 4 - V t) * y t)
    ((continuousOn_const.mul hdy).add (hcoef.mul hy)) hd hdd

/-- Removing the literal common weight preserves C2 regularity on the
positive half-line.  The function remains the original coordinate. -/
theorem spectralHalfPotentialPoissonCLM_physical_coordinate_c2
    (b : SpectralSpace ι) (i : ι) :
    ContDiffOn ℝ 2 (fun s : ℝ => Real.exp (-2 * s) *
      spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b s.toNNReal i)
      (Ioi 0) := by
  have he : ContDiff ℝ 2 (fun s : ℝ => Real.exp (-2 * s)) := by fun_prop
  exact he.contDiffOn.mul
    (spectralHalfPotentialPoissonCLM_coordinate_c2 k hk₀ hk hκ0 hκ1 V hV hV0 b i)

/-- The physical coordinate satisfies the genuine same-potential
equation z'' = (k_i^2 - V) z at every positive time. -/
theorem spectralHalfPotentialPoissonCLM_physical_coordinate_equation
    (b : SpectralSpace ι) (i : ι) (t : ℝ) (ht : 0 < t) :
    let z := fun s : ℝ => Real.exp (-2 * s) *
      spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b s.toNNReal i
    HasDerivAt (deriv z) ((k i ^ 2 - V t) * z t) t := by
  let y : ℝ → ℝ := fun s =>
    spectralHalfPotentialPoissonCLM k hk₀ hk hκ0 hκ1 V hV hV0 b s.toNNReal i
  let z : ℝ → ℝ := fun s => Real.exp (-2 * s) * y s
  have hC2 : ContDiffOn ℝ 2 z (Ioi 0) :=
    spectralHalfPotentialPoissonCLM_physical_coordinate_c2
      k hk₀ hk hκ0 hκ1 V hV hV0 b i
  have hz (s : ℝ) (hs : 0 < s) : HasDerivAt z (deriv z s) s :=
    ((hC2.contDiffAt (isOpen_Ioi.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  have hy (s : ℝ) (hs : 0 < s) : DifferentiableAt ℝ y s ∧
      HasDerivAt (deriv y)
        (4 * deriv y s + ((k i ^ 2 - V s) - 4) * y s + 0) s := by
    have h := spectralHalfPotentialPoissonCLM_coordinate_equation
      k hk₀ hk hκ0 hκ1 V hV hV0 b i s hs
    refine ⟨h.1, h.2.congr_deriv ?_⟩
    ring
  have h := halfEnd_expTwo_forced_physical_derivative_equation
    y z (deriv z) (fun s => k i ^ 2 - V s) (fun _ => 0)
    (fun _ _ => rfl) hz hy t ht
  simpa only [mul_zero, add_zero] using h

#print axioms spectralHalfPotentialPoissonCLM_coordinate_zero
#print axioms spectralHalfPotentialPoissonCLM_coordinate_equation
#print axioms spectralHalfPotentialPoissonCLM_coordinate_c2
#print axioms spectralHalfPotentialPoissonCLM_physical_coordinate_c2
#print axioms spectralHalfPotentialPoissonCLM_physical_coordinate_equation

end Yamabe3.Analysis.Delaunay
