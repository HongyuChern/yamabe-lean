import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndVariational
import Yamabe3.Analysis.NativeWeakChartCompletion
import Yamabe3.Analysis.Cylinder.NativeForcedHalfEndFullGreen

/-!
# One Euclidean completion element for the forced half-end field

The source, weak gradient and completion witness are retained throughout.
The normalized volume source is distinct from the physical Green source.
Only smooth tests, not volume representatives, are evaluated on the sphere.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped NNReal Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Yamabe3.Analysis.Delaunay
open PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak

local notation "D" => nativeWeakEuclideanD

/-- The actual smooth test is a zero-boundary Sobolev test. -/
theorem nativeCompletion_energyTest_memH01 {O : Set E} (hO : IsOpen O)
    (η : EnergyTest D O) : MemH01 (η : E → ℝ) O := by
  exact memW01p_of_contDiff_hasCompactSupport_subset hO η.smooth.contDiff
    η.hasCompactSupport η.support_subset

/-- Zero extension of an L² source defines a continuous linear functional
on the completion, using its actual retained-volume L² map. -/
def nativeCompletionRHS {O : Set E} (hO : IsOpen O) {g : E → ℝ}
    (hg : MemLp g 2 (volume.restrict O)) : H1Zero D O →L[ℝ] ℝ :=
  let hG : MemLp (O.indicator g) 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure := by
    simpa only [native_euclideanMetric_volumeMeasure] using
      (memLp_indicator_iff_restrict hO.measurableSet).mpr hg
  (innerSL ℝ (hG.toLp (O.indicator g))).comp (toL2 D O)

/-- The continuous functional is precisely the restricted integral. -/
theorem nativeCompletionRHS_eq_integral {O : Set E} (hO : IsOpen O) {g : E → ℝ}
    (hg : MemLp g 2 (volume.restrict O)) (η : H1Zero D O) :
    nativeCompletionRHS hO hg η = ∫ x in O, g x * (toL2 D O η : E → ℝ) x := by
  let hG : MemLp (O.indicator g) 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure := by
    simpa only [native_euclideanMetric_volumeMeasure] using
      (memLp_indicator_iff_restrict hO.measurableSet).mpr hg
  change inner ℝ (hG.toLp (O.indicator g)) (toL2 D O η) = _
  rw [L2.inner_def]
  have hae := hG.coeFn_toLp
  simp only [native_euclideanMetric_volumeMeasure] at hae ⊢
  calc
    _ = ∫ x, O.indicator (fun x => g x * (toL2 D O η : E → ℝ) x) x := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
      by_cases h : x ∈ O <;> simp [h, mul_comm]
    _ = _ := integral_indicator hO.measurableSet

/-- The volume product exists as a Bochner integral for every completed test. -/
theorem nativeCompletionRHS_integrable {O : Set E} {g : E → ℝ}
    (hg : MemLp g 2 (volume.restrict O)) (η : H1Zero D O) :
    IntegrableOn (fun x => g x * (toL2 D O η : E → ℝ) x) O := by
  have hη : MemLp (toL2 D O η : E → ℝ) 2 volume := by
    simpa only [native_euclideanMetric_volumeMeasure] using Lp.memLp (toL2 D O η)
  exact hg.integrable_mul (hη.restrict O)

/-- Equality of two continuous functionals extends from the dense smooth
tests, for the already fixed completion element. -/
theorem nativeCompletion_variational_extension {O : Set E} (hO : IsOpen O)
    {g : E → ℝ} (hg : MemLp g 2 (volume.restrict O)) (z_E : H1Zero D O)
    (hs : ∀ η : EnergyTest D O,
      gradientEnergy D O z_E (η : H1Zero D O) =
        ∫ x in O, g x * (toL2 D O (η : H1Zero D O) : E → ℝ) x) :
    ∀ η : H1Zero D O, gradientEnergy D O z_E η =
      ∫ x in O, g x * (toL2 D O η : E → ℝ) x := by
  intro η
  rw [← nativeCompletionRHS_eq_integral hO hg]
  induction η using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((gradientEnergy D O) z_E).continuous
      (nativeCompletionRHS hO hg).continuous
  | ih η => rw [nativeCompletionRHS_eq_integral]; exact hs η

/-- Restriction of the zero-extension identity uses the restricted volume,
not any lower-dimensional boundary measure. -/
theorem nativeCompletion_rep_on_domain {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (z_E : H1Zero D O)
    (hz_E : (toL2 D O z_E : E → ℝ) =ᵐ[volume] O.indicator u) :
    (toL2 D O z_E : E → ℝ) =ᵐ[volume.restrict O] u := by
  filter_upwards [ae_restrict_of_ae hz_E,
    ae_restrict_mem hO.measurableSet] with x hx hmem
  simpa only [Set.indicator_of_mem hmem] using hx

/-- A fixed genuine weak gradient and the existing Sobolev test equation
give the completed variational equation for this same realization. -/
theorem nativeCompletion_variational_of_weak {O : Set E} (hO : IsOpen O)
    {u g : E → ℝ} (hu : MemH01 u O) (hg : MemLp g 2 (volume.restrict O))
    (du : Fin 3 → Lp ℝ 2 (volume.restrict O))
    (hdu : ∀ j, HasWeakPartialDeriv j (du j) u O)
    (hvar : ∀ (v : E → ℝ), MemH01 v O → ∀ (q : Fin 3 → E → ℝ),
      (∀ j, MemLp (q j) 2 (volume.restrict O)) →
      (∀ j, HasWeakPartialDeriv j (q j) v O) →
      (∫ x in O, ∑ j : Fin 3, du j x * q j x) = ∫ x in O, g x * v x)
    (z_E : H1Zero D O)
    (hz_E : (toL2 D O z_E : E → ℝ) =ᵐ[volume] O.indicator u) :
    ∀ η : H1Zero D O, gradientEnergy D O z_E η =
      ∫ x in O, g x * (toL2 D O η : E → ℝ) x := by
  apply nativeCompletion_variational_extension hO hg z_E
  intro η
  let q : Fin 3 → E → ℝ := fun j x =>
    fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single j 1)
  have hq (j : Fin 3) : MemLp (q j) 2 (volume.restrict O) :=
    (nativeEuclidean_test_derivative_memLp O η j).restrict O
  have hwq (j : Fin 3) : HasWeakPartialDeriv j (q j) (η : E → ℝ) O :=
    HasWeakPartialDeriv.of_contDiff hO (η.smooth.contDiff.of_le (by norm_cast))
  rw [nativeEuclidean_memH01_gradient_pairing hO hu (fun j x => du j x)
    (fun j => Lp.memLp (du j)) hdu z_E hz_E]
  change (∑ j : Fin 3, ∫ x in O, du j x * q j x) = _
  have hsum : (∫ x in O, ∑ j : Fin 3, du j x * q j x) =
      ∑ j : Fin 3, ∫ x in O, du j x * q j x := by
    simpa only [Pi.mul_apply] using
      (integral_finsetSum Finset.univ (fun j _ => (Lp.memLp (du j)).integrable_mul (hq j)))
  rw [← hsum]
  rw [hvar η (nativeCompletion_energyTest_memH01 hO η) q hq hwq]
  have hη : (toL2 D O (η : H1Zero D O) : E → ℝ) =ᵐ[volume] (η : E → ℝ) := by
    have ht : (testToL2 D O η : E → ℝ) =ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure]
        (η : E → ℝ) := η.memLp.coeFn_toLp
    simpa only [toL2_coe, native_euclideanMetric_volumeMeasure] using ht
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hη] with x hx
  rw [hx]

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

/-- One choice of the original weak gradient and one Euclidean completion
element simultaneously retain every test equation, energy bound and physical
model Green formula. The source representative is called `q_src`, never `z_E`.
The quantifier over both smooth and completed tests is inside this single
existential. No weak equation or completion witness is an input. -/
theorem native_forced_halfEnd_completion_variational_green
    (F : ℝ≥0 →ᵇ AngularL2) {w q_src : ℝ × S → ℝ}
    (hw : Measurable w) (hq_src : Measurable q_src)
    (hwAE : ∀ t, (fun θ => w (t, θ)) =ᵐ[angularVolume]
      (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t : S → ℝ))
    (hq_srcAE : ∀ t, (fun θ => q_src (t, θ)) =ᵐ[angularVolume]
      (nativeHighProjection (F t.toNNReal) : S → ℝ)) :
    let u := cylinderLift w
    let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * q_src p)
    let g_norm := fun x : E => f x / 8 + nativeHalfEndPotentialCoefficient V x * u x
    let O := Metric.ball (0 : E) 1 \ {(0 : E)}
    MemH01 u O ∧
    MemLp g_norm 2 (volume.restrict O) ∧
    IntegrableOn (fun x : E => g_norm x ^ 2) O ∧
    (∫ x in O, g_norm x ^ 2) ≤
      (1 + ‖V‖ ^ 2 * (2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2) * ‖F‖ ^ 2 ∧
    ∃ du : Fin 3 → Lp ℝ 2 (volume.restrict O),
    ∃ z_E : H1Zero D O,
      (∀ j, HasWeakPartialDeriv j (du j) u O) ∧
      (toL2 D O z_E : E → ℝ) =ᵐ[volume] O.indicator u ∧
      (toL2 D O z_E : E → ℝ) =ᵐ[volume.restrict O] u ∧
      (∀ η : EnergyTest D O,
        gradientEnergy D O z_E (η : H1Zero D O) =
          ∑ j : Fin 3, ∫ x in O, du j x *
            fderiv ℝ (η : E → ℝ) x (EuclideanSpace.single j 1)) ∧
      (∀ η : H1Zero D O,
        IntegrableOn (fun x => g_norm x * (toL2 D O η : E → ℝ) x) O ∧
        gradientEnergy D O z_E η = ∫ x in O, g_norm x * (toL2 D O η : E → ℝ) x) ∧
      gradientEnergy D O z_E z_E = ∫ x in O, g_norm x * (toL2 D O z_E : E → ℝ) x ∧
      IntegrableOn (fun x : E => ∑ j : Fin 3, du j x ^ 2) O ∧
      IntegrableOn (fun x : E => g_norm x * u x) O ∧
      gradientEnergy D O z_E z_E = ∫ x in O, ∑ j : Fin 3, du j x ^ 2 ∧
      gradientEnergy D O z_E z_E = ∫ x in O, g_norm x * u x ∧
      gradientEnergy D O z_E z_E ≤
        (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
          nativeHalfHighDirichletDerivativeBound κ V ^ 2) * ‖F‖ ^ 2 / 2 ∧
      ‖z_E‖ ^ 2 = (∫ x in O, u x ^ 2) + ∑ j : Fin 3, ∫ x in O, du j x ^ 2 ∧
      IntegrableOn (fun x : E => u x ^ 2 + (∑ j : Fin 3, du j x ^ 2)) O ∧
      ‖z_E‖ ^ 2 = ∫ x in O, u x ^ 2 + (∑ j : Fin 3, du j x ^ 2) ∧
      ‖z_E‖ ^ 2 ≤
        ((2 / (((5 / 2 : ℝ) ^ 2 - 4) * (1 - κ) ^ 2)) ^ 2 / 6 +
          (nativeHalfHighDirichletEnergyBound κ V ^ 2 +
            nativeHalfHighDirichletDerivativeBound κ V ^ 2) / 2) * ‖F‖ ^ 2 ∧
      (∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (0 : E) ∉ tsupport φ →
        IntegrableOn (fun x : E => (toL2 D O z_E : E → ℝ) x *
          (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x)) O ∧
        IntegrableOn (fun x : E => f x * φ x) O ∧
        (∫ x in O, (toL2 D O z_E : E → ℝ) x *
          (-8 * euclideanD.laplacian φ x - 8 * nativeHalfEndPotentialCoefficient V x * φ x)) =
        (∫ x in O, f x * φ x) +
          ∫ θ : S, φ (θ : E) *
            (((-8 : ℝ) • nativeHalfHighDirichletEntranceDerivativeCLM
              hκ0 hκ1 V hV hV0 F : AngularL2) : S → ℝ) θ ∂angularVolume) := by
  let u := cylinderLift w
  let f := physicalForcing (fun p : ℝ × S => Real.exp (-2 * p.1) * q_src p)
  let g_norm := fun x : E => f x / 8 + nativeHalfEndPotentialCoefficient V x * u x
  let O := Metric.ball (0 : E) 1 \ {(0 : E)}
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  obtain ⟨hu, hg, hgI, hgBound, du, hdu, hvar, hgradI, hselfI,
      hselfEq, hgradBound, htotalI, htotalBound⟩ :=
    native_forced_halfEnd_global_variational_equation
      hκ0 hκ1 V hV hV0 F hw hq_src hwAE hq_srcAE
  obtain ⟨z_E, hz_E, hsmooth⟩ := exists_nativeEuclideanH01_of_memH01_with_gradient
    hO hu (fun j x => du j x) (fun j => Lp.memLp (du j)) hdu
  have hrep : (toL2 D O z_E : E → ℝ) =ᵐ[volume.restrict O] u :=
    nativeCompletion_rep_on_domain hO z_E hz_E
  have hall : ∀ η : H1Zero D O, gradientEnergy D O z_E η =
      ∫ x in O, g_norm x * (toL2 D O η : E → ℝ) x :=
    nativeCompletion_variational_of_weak hO hu hg du hdu
      (fun v hv q hq hwq => (hvar v hv q hq hwq).2.2) z_E hz_E
  have hself : gradientEnergy D O z_E z_E = ∫ x in O, g_norm x * u x := by
    rw [hall]
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx]
  have hgrad : gradientEnergy D O z_E z_E = ∫ x in O, ∑ j : Fin 3, du j x ^ 2 :=
    hself.trans hselfEq.symm
  have hnorm : ‖z_E‖ ^ 2 = (∫ x in O, u x ^ 2) +
      ∑ j : Fin 3, ∫ x in O, du j x ^ 2 :=
    nativeEuclidean_memH01_norm_sq hO hu (fun j x => du j x)
      (fun j => Lp.memLp (du j)) hdu z_E hz_E
  have hsum : (∫ x in O, ∑ j : Fin 3, du j x ^ 2) =
      ∑ j : Fin 3, ∫ x in O, du j x ^ 2 :=
    integral_finsetSum Finset.univ (fun j _ => (Lp.memLp (du j)).integrable_sq)
  have hnormTotal : ‖z_E‖ ^ 2 = ∫ x in O, u x ^ 2 + (∑ j : Fin 3, du j x ^ 2) := by
    rw [integral_add hu.1.1.integrable_sq hgradI, hsum]
    exact hnorm
  refine ⟨hu, hg, hgI, hgBound, du, z_E, hdu, hz_E, hrep, hsmooth,
    (fun η => ⟨nativeCompletionRHS_integrable hg η, hall η⟩), hall z_E,
    hgradI, hselfI, hgrad, hself, ?_, hnorm, htotalI, hnormTotal, ?_, ?_⟩
  · rw [hgrad]
    exact hgradBound
  · rw [hnormTotal]
    exact htotalBound
  · intro φ hφ hc hzero
    exact native_forced_halfEnd_original_physical_green_ae
      hκ0 hκ1 V hV hV0 F hw hq_src hwAE hq_srcAE hrep
      (Filter.EventuallyEq.refl _ _) hφ hc hzero

#print axioms native_forced_halfEnd_completion_variational_green

end Yamabe3.Analysis.SpherePolar
