import Yamabe3.Analysis.NativeForcedHalfEndDerivativeOperator
import Yamabe3.Analysis.Cylinder.NativeCylinderHilbertNorm
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Actual disappearance of the original field at the Dirichlet entrance

The original curve has its already produced strong right derivative on
`Ici 0`, has value zero at the entrance, and has the proved weighted
derivative bound.  The genuine mean-value inequality therefore gives
`norm U(t) <= CD * norm F * t` for every nonnegative time.

On `Ioo 0 delta` the actual weighted square is integrable before any
comparison is made.  Since `exp(-2t) <= 1` there, integrating the square
of the linear disappearance rate gives `CD^2 * norm F^2 * delta^3 / 3`.
The exact existing polar identity gives the same bound for the original
physical representative on `cylinderShell 0 delta`.

These are estimates for the same original Hilbert curve and physical
function.  No zero-boundary Sobolev membership or trace identification
is asserted by this file.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The original actual right derivative and zero entrance produce a
linear norm bound at every nonnegative time. -/
theorem nativeHalfHighDirichletPhysical_norm_le_time
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : 0 ≤ t) :
    ‖nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t‖ ≤
      nativeHalfHighDirichletDerivativeBound κ V * ‖F‖ * t := by
  let U := nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F
  let D := nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F
  let C : ℝ := nativeHalfHighDirichletDerivativeBound κ V * ‖F‖
  have hbound (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) : ‖D r‖ ≤ C := by
    have hw : Real.exp (2 * r) * ‖D r‖ ≤ C := by
      simpa only [D, C, nativeHalfHighDirichletDerivativeBound] using
        nativeHalfHighDirichletPhysicalDerivative_weighted_norm_le hκ0 hκ1 V hV hV0 F r hr
    calc
      _ = 1 * ‖D r‖ := (one_mul _).symm
      _ ≤ Real.exp (2 * r) * ‖D r‖ :=
        mul_le_mul_of_nonneg_right
          (Real.one_le_exp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)) (norm_nonneg _)
      _ ≤ C := hw
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := U) (f' := D) (s := Ici (0 : ℝ)) (C := C) (x := 0) (y := t)
    (fun r hr => nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 F r hr)
    hbound (convex_Ici (0 : ℝ)) (by simp) ht
  have hzero : U 0 = 0 :=
    nativeHalfHighDirichletPhysical_zero_of_nonpos hκ0 hκ1 V hV hV0 F 0 le_rfl
  simpa only [hzero, sub_zero, Real.norm_of_nonneg ht, C] using hmean

/-- The true weighted square integral on a short positive-time layer
has the cubic bound produced from the original derivative constant.
Integrability is established on the compact interval before restriction
and before the integral comparison. -/
theorem nativeHalfHighDirichletPhysical_boundary_layer_integral_le
    (F : ℝ≥0 →ᵇ AngularL2) (δ : ℝ) (hδ : 0 ≤ δ) :
    IntegrableOn (fun t : ℝ => Real.exp (-2 * t) *
      ‖nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t‖ ^ 2) (Ioo 0 δ) ∧
    (∫ t in Ioo (0 : ℝ) δ, Real.exp (-2 * t) *
      ‖nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t‖ ^ 2) ≤
      nativeHalfHighDirichletDerivativeBound κ V ^ 2 * ‖F‖ ^ 2 * δ ^ 3 / 3 := by
  let U := nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F
  let C : ℝ := nativeHalfHighDirichletDerivativeBound κ V * ‖F‖
  have hU : Continuous U := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  have hIcc : IntegrableOn (fun t : ℝ => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Icc 0 δ) :=
    (((show Continuous (fun t : ℝ => Real.exp (-2 * t)) by fun_prop).mul
      (hU.norm.pow 2)).integrableOn_Icc)
  have hI : IntegrableOn (fun t : ℝ => Real.exp (-2 * t) * ‖U t‖ ^ 2) (Ioo 0 δ) :=
    hIcc.mono_set Ioo_subset_Icc_self
  have hBC : Continuous (fun t : ℝ => C ^ 2 * t ^ 2) := by fun_prop
  have hBcc : IntegrableOn (fun t : ℝ => C ^ 2 * t ^ 2) (Icc 0 δ) := hBC.integrableOn_Icc
  have hB : IntegrableOn (fun t : ℝ => C ^ 2 * t ^ 2) (Ioo 0 δ) :=
    hBcc.mono_set Ioo_subset_Icc_self
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) δ) :
      Real.exp (-2 * t) * ‖U t‖ ^ 2 ≤ C ^ 2 * t ^ 2 := by
    have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    have hlinear : ‖U t‖ ≤ C * t :=
      nativeHalfHighDirichletPhysical_norm_le_time hκ0 hκ1 V hV hV0 F t ht.1.le
    calc
      _ ≤ ‖U t‖ ^ 2 :=
        (mul_le_mul_of_nonneg_right he (sq_nonneg _)).trans_eq (one_mul _)
      _ ≤ (C * t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlinear 2
      _ = C ^ 2 * t ^ 2 := mul_pow _ _ 2
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ t in Ioo (0 : ℝ) δ, C ^ 2 * t ^ 2 :=
      setIntegral_mono_on hI hB measurableSet_Ioo hpoint
    _ = C ^ 2 * δ ^ 3 / 3 := by
      rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hδ, integral_pow]
      norm_num <;> ring
    _ = _ := by dsimp only [C]; ring

end Yamabe3.Analysis.Delaunay

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- The same original physical representative has the genuine cubic
square-integral bound on its boundary shell.  The physical L2 and square
integrability are produced, and the original polar identity supplies
the passage from the actual Hilbert curve. -/
theorem native_forced_halfEnd_boundary_shell_value_sq_le
    (F : ℝ≥0 →ᵇ AngularL2) {w : ℝ × S → ℝ} (hw : Measurable w)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (δ : ℝ) (hδ : 0 ≤ δ) :
    MemLp (cylinderLift w) 2 (volume.restrict (cylinderShell 0 δ)) ∧
    IntegrableOn (fun x : E => cylinderLift w x ^ 2) (cylinderShell 0 δ) ∧
    (∫ x in cylinderShell 0 δ, cylinderLift w x ^ 2) ≤
      nativeHalfHighDirichletDerivativeBound κ V ^ 2 * ‖F‖ ^ 2 * δ ^ 3 / 3 := by
  have hU := nativeHalfHighDirichletPhysical_continuous hκ0 hκ1 V hV hV0 F
  have hLp := memLp_cylinderLift_on_shell hw 0 δ (native_joint_memLp_interval hU hw hwAE 0 δ)
  refine ⟨hLp, hLp.integrable_sq, ?_⟩
  calc
    _ = ∫ t in Icc (0 : ℝ) δ, Real.exp (-2 * t) *
        ‖nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t‖ ^ 2 :=
      integral_cylinderLift_sq_shell_eq hU hw hwAE 0 δ
    _ = ∫ t in Ioo (0 : ℝ) δ, Real.exp (-2 * t) *
        ‖nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t‖ ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    _ ≤ _ := (nativeHalfHighDirichletPhysical_boundary_layer_integral_le
      hκ0 hκ1 V hV hV0 F δ hδ).2

#print axioms nativeHalfHighDirichletPhysical_norm_le_time
#print axioms nativeHalfHighDirichletPhysical_boundary_layer_integral_le
#print axioms native_forced_halfEnd_boundary_shell_value_sq_le

end Yamabe3.Analysis.SpherePolar
