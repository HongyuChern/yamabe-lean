import Yamabe3.Analysis.NativeHighAngularRoot
import Yamabe3.Analysis.SpectralFirstDerivativeKernel
import PoincareLib.Analysis.Parabolic.Dirichlet.SpectralSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual free high-mode half-end Poisson data

The native Hilbert basis and its actual eigenvalues construct exp(-t A)
on the high spectral projection.  The curve has its literal projected
boundary value at t=0.  For a genuine native H1 boundary function, the
previously constructed high square root belongs to L2 and supplies a
continuous strong derivative curve.  An actual Hilbert-valued interval
integral identifies that derivative up to and including the right endpoint
at t=0.  No operator-norm continuity at zero is used.

This is the free high angular equation.  A Delaunay potential, its zero
Dirichlet correction, low-mode parameters, and a coupled inverse are not
conclusions of this file.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum
open Poincare.Analysis.Dirichlet.Spectral

private def nativeAngularNonnegativeRate (i : AngularIndex) : ℝ≥0 :=
  ⟨nativeAngularRate i, by have := nativeAngularRate_lower i; linarith⟩

private theorem native_rate_heat_coefficient (t : ℝ≥0) (u : AngularL2) (i : AngularIndex) :
    inner ℝ (angularBasis i) (heat angularBasis nativeAngularNonnegativeRate t u) =
      Real.exp (-nativeAngularRate i * (t : ℝ)) * inner ℝ (angularBasis i) u := by
  have h := heat_repr angularBasis nativeAngularNonnegativeRate t u i
  rw [show (nativeAngularNonnegativeRate i : ℝ) = nativeAngularRate i from rfl] at h
  simpa only [HilbertBasis.repr_apply_apply] using h

private theorem native_rate_heat_norm_le (t : ℝ≥0) (u : AngularL2) :
    ‖heat angularBasis nativeAngularNonnegativeRate t u‖ ≤
      Real.exp (-(5 / 2 : ℝ) * (t : ℝ)) * ‖u‖ := by
  have he : angularBasis.repr (heat angularBasis nativeAngularNonnegativeRate t u) =
      spectralPoissonKernel nativeAngularRate (by norm_num) nativeAngularRate_lower
        (t : ℝ) (angularBasis.repr u) := by
    ext i
    rw [heat_repr, spectralPoissonKernel_apply, abs_of_nonneg t.coe_nonneg]
    rfl
  rw [← angularBasis.repr.norm_map (heat angularBasis nativeAngularNonnegativeRate t u), he]
  calc
    _ ≤ ‖spectralPoissonKernel nativeAngularRate (by norm_num) nativeAngularRate_lower
        (t : ℝ)‖ * ‖angularBasis.repr u‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.exp (-(5 / 2 : ℝ) * |(t : ℝ)|) * ‖angularBasis.repr u‖ :=
      mul_le_mul_of_nonneg_right
        (spectralPoissonKernel_norm_le nativeAngularRate (by norm_num)
          nativeAngularRate_lower (t : ℝ)) (norm_nonneg _)
    _ = _ := by rw [abs_of_nonneg t.coe_nonneg, LinearIsometryEquiv.norm_map]

/-- The free high-mode Poisson evolution of the actual angular L2 data. -/
def nativeHighFreePoisson (t : ℝ≥0) : AngularL2 →L[ℝ] AngularL2 :=
  (heat angularBasis nativeAngularNonnegativeRate t).comp nativeHighProjection

theorem nativeHighFreePoisson_coefficient (t : ℝ≥0) (u : AngularL2) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeHighFreePoisson t u) =
      Real.exp (-nativeAngularRate i * (t : ℝ)) *
        (if 6 ≤ angularEigenvalue i then inner ℝ (angularBasis i) u else 0) := by
  change inner ℝ (angularBasis i)
    (heat angularBasis nativeAngularNonnegativeRate t (nativeHighProjection u)) = _
  rw [native_rate_heat_coefficient, nativeHighProjection, nativeAngularProjection_coefficient]

theorem nativeHighFreePoisson_zero : nativeHighFreePoisson 0 = nativeHighProjection := by
  unfold nativeHighFreePoisson
  rw [heat_zero]
  rfl

theorem nativeHighFreePoisson_apply_norm_le (t : ℝ≥0) (u : AngularL2) :
    ‖nativeHighFreePoisson t u‖ ≤ Real.exp (-(5 / 2 : ℝ) * (t : ℝ)) * ‖u‖ := by
  exact (native_rate_heat_norm_le t (nativeHighProjection u)).trans
    (mul_le_mul_of_nonneg_left
      (nativeAngularProjection_apply_norm_le _ u) (Real.exp_pos _).le)

theorem nativeHighFreePoisson_norm_le (t : ℝ≥0) :
    ‖nativeHighFreePoisson t‖ ≤ Real.exp (-(5 / 2 : ℝ) * (t : ℝ)) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
    (nativeHighFreePoisson_apply_norm_le t)

theorem nativeHighFreePoisson_continuous (u : AngularL2) :
    Continuous (fun t : ℝ≥0 => nativeHighFreePoisson t u) :=
  continuous_heat angularBasis nativeAngularNonnegativeRate (nativeHighProjection u)

theorem nativeHighFreePoisson_high (t : ℝ≥0) (u : AngularL2) :
    nativeHighProjection (nativeHighFreePoisson t u) = nativeHighFreePoisson t u := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighProjection, nativeAngularProjection_coefficient,
    nativeHighFreePoisson_coefficient]
  split_ifs <;> simp

/-- Every actual coefficient of the same high Poisson curve satisfies the
free native angular equation.  The low coordinates vanish identically. -/
theorem nativeHighFreePoisson_coordinate_equation (u : AngularL2)
    (i : AngularIndex) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (deriv (fun s : ℝ => inner ℝ (angularBasis i)
        (nativeHighFreePoisson s.toNNReal u)))
      ((angularEigenvalue i + 1 / 4) * inner ℝ (angularBasis i)
        (nativeHighFreePoisson t.toNNReal u)) t := by
  let c : ℝ := if 6 ≤ angularEigenvalue i then inner ℝ (angularBasis i) u else 0
  let q : ℝ → ℝ := fun s => Real.exp (-nativeAngularRate i * s) * c
  let y : ℝ → ℝ := fun s => inner ℝ (angularBasis i) (nativeHighFreePoisson s.toNNReal u)
  have heq : y =ᶠ[𝓝 t] q := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    dsimp only [y, q, c]
    rw [nativeHighFreePoisson_coefficient, Real.coe_toNNReal s hs.le]
  have hd (s : ℝ) : HasDerivAt q
      ((-nativeAngularRate i * Real.exp (-nativeAngularRate i * s)) * c) s := by
    apply (((hasDerivAt_id s).const_mul (-nativeAngularRate i)).exp.mul_const c).congr_deriv
    simp only [id_eq, mul_one, one_mul]
    ring
  have hder : deriv q = fun s =>
      (-nativeAngularRate i * Real.exp (-nativeAngularRate i * s)) * c :=
    funext (fun s => (hd s).deriv)
  have hd2 : HasDerivAt (deriv q) (nativeAngularRate i ^ 2 * q t) t := by
    rw [hder]
    apply ((((hasDerivAt_id t).const_mul (-nativeAngularRate i)).exp.const_mul
      (-nativeAngularRate i)).mul_const c).congr_deriv
    dsimp only [q]
    simp only [id_eq, mul_one, one_mul]
    ring
  change HasDerivAt (deriv y) ((angularEigenvalue i + 1 / 4) * y t) t
  apply (hd2.congr_of_eventuallyEq heq.deriv).congr_deriv
  rw [heq.self_of_nhds]
  dsimp only [q, c]
  by_cases hi : 6 ≤ angularEigenvalue i
  · rw [if_pos hi, nativeAngularRate_sq, max_eq_right hi]
  · simp only [if_neg hi, mul_zero]

/-- The actual strong derivative candidate for native H1 boundary data. -/
def nativeHighFreePoissonDerivative (u : AngularH1) (t : ℝ) : AngularL2 :=
  -heat angularBasis nativeAngularNonnegativeRate t.toNNReal (nativeHighAngularRootCLM u)

theorem nativeHighFreePoissonDerivative_continuous (u : AngularH1) :
    Continuous (nativeHighFreePoissonDerivative u) := by
  exact ((continuous_heat angularBasis nativeAngularNonnegativeRate
    (nativeHighAngularRootCLM u)).comp continuous_real_toNNReal).neg

theorem nativeHighFreePoissonDerivative_coefficient (u : AngularH1) (t : ℝ)
    (ht : 0 ≤ t) (i : AngularIndex) :
    inner ℝ (angularBasis i) (nativeHighFreePoissonDerivative u t) =
      (-nativeAngularRate i * Real.exp (-nativeAngularRate i * t)) *
        inner ℝ (angularBasis i) (nativeHighProjection (angularEmbedding u)) := by
  rw [nativeHighFreePoissonDerivative, inner_neg_right, native_rate_heat_coefficient,
    Real.coe_toNNReal t ht, nativeHighAngularRootCLM_eq_rate_high_coefficient]
  ring

theorem nativeHighFreePoisson_integral_derivative (u : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, nativeHighFreePoissonDerivative u s) =
      nativeHighFreePoisson t.toNNReal (angularEmbedding u) -
        nativeHighProjection (angularEmbedding u) := by
  have hV := nativeHighFreePoissonDerivative_continuous u
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  let ev : AngularL2 →L[ℝ] ℝ := innerSL ℝ (angularBasis i)
  change ev (∫ s in (0 : ℝ)..t, nativeHighFreePoissonDerivative u s) =
    ev (nativeHighFreePoisson t.toNNReal (angularEmbedding u) -
      nativeHighProjection (angularEmbedding u))
  rw [map_sub, ← ev.intervalIntegral_comp_comm (hV.intervalIntegrable _ _)]
  let c := inner ℝ (angularBasis i) (nativeHighProjection (angularEmbedding u))
  have hder (s : ℝ) : HasDerivAt
      (fun x : ℝ => Real.exp (-nativeAngularRate i * x) * c)
      ((-nativeAngularRate i * Real.exp (-nativeAngularRate i * s)) * c) s := by
    apply (((hasDerivAt_id s).const_mul (-nativeAngularRate i)).exp.mul_const c).congr_deriv
    simp only [id_eq, mul_one, one_mul]
    ring
  calc
    _ = ∫ s in (0 : ℝ)..t,
        (-nativeAngularRate i * Real.exp (-nativeAngularRate i * s)) * c := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := (Set.mem_uIcc.mp hs).elim (fun h => h.1) (fun h => le_trans ht h.1)
      exact nativeHighFreePoissonDerivative_coefficient u s hs0 i
    _ = Real.exp (-nativeAngularRate i * t) * c - c := by
      have hc : Continuous (fun s : ℝ =>
          (-nativeAngularRate i * Real.exp (-nativeAngularRate i * s)) * c) := by fun_prop
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hder s) (hc.intervalIntegrable 0 t)
    _ = _ := by
      change _ = inner ℝ (angularBasis i) (nativeHighFreePoisson t.toNNReal (angularEmbedding u)) - c
      rw [nativeHighFreePoisson_coefficient, Real.coe_toNNReal t ht]
      dsimp only [c]
      rw [nativeHighProjection, nativeAngularProjection_coefficient]

/-- Genuine strong Hilbert differentiation on the closed half-line,
including the right derivative at its entrance. -/
theorem nativeHighFreePoisson_hasDerivWithinAt (u : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => nativeHighFreePoisson s.toNNReal (angularEmbedding u))
      (nativeHighFreePoissonDerivative u t) (Ici 0) t := by
  have hV := nativeHighFreePoissonDerivative_continuous u
  have hd : HasDerivAt
      (fun x : ℝ => nativeHighProjection (angularEmbedding u) +
        ∫ s in (0 : ℝ)..x, nativeHighFreePoissonDerivative u s)
      (nativeHighFreePoissonDerivative u t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right (hV.intervalIntegrable _ _)
      hV.aestronglyMeasurable.stronglyMeasurableAtFilter hV.continuousAt).const_add _
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro s hs
  rw [nativeHighFreePoisson_integral_derivative u s hs]
  abel

theorem nativeHighFreePoisson_hasDerivAt (u : AngularH1) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => nativeHighFreePoisson s.toNNReal (angularEmbedding u))
      (nativeHighFreePoissonDerivative u t) t :=
  (nativeHighFreePoisson_hasDerivWithinAt u t ht.le).hasDerivAt (Ici_mem_nhds ht)

theorem nativeHighFreePoisson_boundary_derivative (u : AngularH1) :
    HasDerivWithinAt (fun s : ℝ => nativeHighFreePoisson s.toNNReal (angularEmbedding u))
      (-nativeHighAngularRootCLM u) (Ici 0) 0 := by
  simpa only [nativeHighFreePoissonDerivative, Real.toNNReal_zero, heat_zero,
    ContinuousLinearMap.id_apply] using nativeHighFreePoisson_hasDerivWithinAt u 0 le_rfl

theorem nativeHighFreePoissonDerivative_norm_le (u : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    ‖nativeHighFreePoissonDerivative u t‖ ≤ Real.exp (-(5 / 2 : ℝ) * t) * ‖u‖ := by
  rw [nativeHighFreePoissonDerivative, norm_neg]
  exact (native_rate_heat_norm_le t.toNNReal (nativeHighAngularRootCLM u)).trans
    (by rw [Real.coe_toNNReal t ht]
        exact mul_le_mul_of_nonneg_left (nativeHighAngularRootCLM_apply_norm_le u)
          (Real.exp_pos _).le)

/-- A true native H1 datum has uniformly controlled value and strong
time derivative in the common exp(2t) weighted topology on t >= 0. -/
theorem nativeHighFreePoisson_weighted_cauchy (u : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (2 * t) * ‖nativeHighFreePoisson t.toNNReal (angularEmbedding u)‖ ≤ ‖u‖ ∧
    Real.exp (2 * t) * ‖nativeHighFreePoissonDerivative u t‖ ≤ ‖u‖ := by
  have hE : Real.exp (2 * t) * Real.exp (-(5 / 2 : ℝ) * t) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    linarith
  have hEmb : ‖angularEmbedding u‖ ≤ ‖u‖ :=
    PoincareMT.LeviCivitaData.Dirichlet.norm_toDomainL2_le u
  constructor
  · have h := nativeHighFreePoisson_apply_norm_le t.toNNReal (angularEmbedding u)
    rw [Real.coe_toNNReal t ht] at h
    calc
      _ ≤ Real.exp (2 * t) * (Real.exp (-(5 / 2 : ℝ) * t) * ‖angularEmbedding u‖) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ ≤ ‖angularEmbedding u‖ := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_left (norm_nonneg _) hE
      _ ≤ ‖u‖ := hEmb
  · calc
      _ ≤ Real.exp (2 * t) * (Real.exp (-(5 / 2 : ℝ) * t) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (nativeHighFreePoissonDerivative_norm_le u t ht)
          (Real.exp_pos _).le
      _ ≤ ‖u‖ := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_left (norm_nonneg _) hE

#print axioms nativeHighFreePoisson
#print axioms nativeHighFreePoisson_boundary_derivative
#print axioms nativeHighFreePoisson_weighted_cauchy

end Yamabe3.Analysis.Delaunay
