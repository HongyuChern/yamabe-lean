import Yamabe3.Analysis.NativeRestrictedEnergyLimit
import Yamabe3.Analysis.NativeDomainSupportedMultiplier
import Yamabe3.Analysis.NativeShiftedExteriorCutoff
import Yamabe3.Analysis.NativeExteriorSphereGreen
import Yamabe3.Analysis.Green.NativeChartOperatorTransfer

/-!
# Actual exterior restriction of a native element with zero sphere trace

The radial cutoffs are the literal shifted chart cutoffs. This file first
computes their gradient cost in the original metric and controls differences
of their actual native energy multipliers. The support lies in the exterior
of the deleted closed chart ball. The intended restriction is the limit of
these products applied to the same original completed element.

This construction does not identify the global trace kernel with the
exterior H1-zero space: it removes the original field inside the ball.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory Metric UniformSpace
open scoped Topology ContDiff Manifold Bundle InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def exteriorRestrictionH1NormedSpace (g : RiemannianMetric 3 M) (Ω : Set M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData Ω) := inferInstance
attribute [local instance] exteriorRestrictionH1NormedSpace

/-- The actual native gradient product estimate is retained under
subtraction of two smooth multipliers. -/
private theorem native_gradient_sub_sq_le
    (g : RiemannianMetric 3 M) {χ ψ : M → ℝ}
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hψ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ψ) (x : M) :
    g.inner x (g.leviCivitaData.gradient (fun y => χ y - ψ y) x)
      (g.leviCivitaData.gradient (fun y => χ y - ψ y) x) ≤
      2 * g.inner x (g.leviCivitaData.gradient χ x) (g.leviCivitaData.gradient χ x) +
      2 * g.inner x (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient ψ x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsub : g.leviCivitaData.gradient (fun y => χ y - ψ y) x =
      g.leviCivitaData.gradient χ x - g.leviCivitaData.gradient ψ x := by
    apply (g.inner_isInvertible x).injective
    ext v
    simp only [g.leviCivitaData.inner_gradient, map_sub, sub_apply]
    exact congrArg (fun L => L v)
      (mvfderiv_sub ((hχ x).mdifferentiableAt (by simp))
        ((hψ x).mdifferentiableAt (by simp)))
  change inner ℝ (g.leviCivitaData.gradient (fun y => χ y - ψ y) x)
      (g.leviCivitaData.gradient (fun y => χ y - ψ y) x) ≤
    2 * inner ℝ (g.leviCivitaData.gradient χ x) (g.leviCivitaData.gradient χ x) +
    2 * inner ℝ (g.leviCivitaData.gradient ψ x) (g.leviCivitaData.gradient ψ x)
  rw [hsub, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  have hn := norm_sub_le (g.leviCivitaData.gradient χ x)
    (g.leviCivitaData.gradient ψ x)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  nlinarith only [hsq, sq_nonneg
    (‖g.leviCivitaData.gradient χ x‖ - ‖g.leviCivitaData.gradient ψ x‖)]

/-- A direct restricted-volume bound for the same completed multiplier.
The assumptions are pointwise bounds on the actual smooth coefficient
and its actual native gradient; they are supplied for the concrete chart
cutoffs below. -/
theorem native_energyMulSmooth_two_domain_norm_sq_le
    (g : RiemannianMetric 3 M) (Ω Λ : Set M)
    (hΩ : MeasurableSet Ω) (hΛ : MeasurableSet Λ)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (A B : ℝ)
    (hv : ∀ x, χ x ^ 2 ≤ Ω.indicator (fun _ => (1 : ℝ)) x +
      Λ.indicator (fun _ => (1 : ℝ)) x)
    (hg : ∀ x, g.inner x (g.leviCivitaData.gradient χ x)
      (g.leviCivitaData.gradient χ x) ≤ A * Ω.indicator (fun _ => (1 : ℝ)) x +
        B * Λ.indicator (fun _ => (1 : ℝ)) x)
    (w : H1Zero g.leviCivitaData univ) :
    ‖energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) χ hχ w‖ ^ 2 ≤
      (1 + 2 * A) * ‖nativeRestrictedL2CLM g Ω w‖ ^ 2 +
      (1 + 2 * B) * ‖nativeRestrictedL2CLM g Λ w‖ ^ 2 +
      2 * (nativeRestrictedGradientEnergy g Ω w w + nativeRestrictedGradientEnergy g Λ w w) := by
  induction w using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih f =>
    rw [energyMulSmooth_coe, Completion.norm_coe,
      nativeRestrictedL2CLM_norm_sq_coe, nativeRestrictedL2CLM_norm_sq_coe,
      nativeRestrictedGradientEnergy_coe, nativeRestrictedGradientEnergy_coe]
    let G : M → ℝ := fun x => g.inner x
      (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient f x)
    have hGn (x : M) : 0 ≤ G x := by
      by_cases hz : g.leviCivitaData.gradient f x = 0
      · simp [G, hz]
      · exact (g.pos x _ hz).le
    have hfi : Integrable (fun x => f x ^ 2) g.volumeMeasure := f.memLp.integrable_sq
    have hGi : Integrable G g.volumeMeasure := f.integrable_gradient f
    let HΩ : M → ℝ := fun x => (1 + 2 * A) * f x ^ 2 + 2 * G x
    let HΛ : M → ℝ := fun x => (1 + 2 * B) * f x ^ 2 + 2 * G x
    have hΩi : Integrable HΩ g.volumeMeasure := (hfi.const_mul _).add (hGi.const_mul _)
    have hΛi : Integrable HΛ g.volumeMeasure := (hfi.const_mul _).add (hGi.const_mul _)
    have hpoint (x : M) :
        f.mulSmooth χ hχ x * f.mulSmooth χ hχ x +
          g.inner x (g.leviCivitaData.gradient (f.mulSmooth χ hχ) x)
            (g.leviCivitaData.gradient (f.mulSmooth χ hχ) x) ≤
        Ω.indicator HΩ x + Λ.indicator HΛ x := by
      have hm := gradient_mul_energy_le χ hχ f x
      have hval := mul_le_mul_of_nonneg_right (hv x) (sq_nonneg (f x))
      have hgrad := mul_le_mul_of_nonneg_right (hv x) (hGn x)
      have hcoef := mul_le_mul_of_nonneg_left (hg x) (sq_nonneg (f x))
      dsimp only [EnergyTest.mulSmooth_apply] at *
      by_cases hxΩ : x ∈ Ω <;> by_cases hxΛ : x ∈ Λ <;>
        simp only [hxΩ, hxΛ, indicator_of_mem, indicator_of_notMem,
          not_false_eq_true, HΩ, HΛ, G] at * <;> nlinarith only [hm, hval, hgrad, hcoef]
    have hI := integral_mono
      (((f.mulSmooth χ hχ).integrable_mul _).add ((f.mulSmooth χ hχ).integrable_gradient _))
      ((hΩi.indicator hΩ).add (hΛi.indicator hΛ)) hpoint
    simp only [Pi.add_apply] at hI
    rw [integral_add ((f.mulSmooth χ hχ).integrable_mul (f.mulSmooth χ hχ))
      ((f.mulSmooth χ hχ).integrable_gradient (f.mulSmooth χ hχ)),
      integral_add (hΩi.indicator hΩ) (hΛi.indicator hΛ),
      integral_indicator hΩ, integral_indicator hΛ] at hI
    rw [EnergyTest.norm_sq, energyInner]
    dsimp only [HΩ, HΛ] at hI
    rw [integral_add (hfi.integrableOn.const_mul _) (hGi.integrableOn.const_mul _),
      integral_add (hfi.integrableOn.const_mul _) (hGi.integrableOn.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul] at hI
    dsimp only [G] at hI
    linarith only [hI]

/-- Subtraction in the coefficient agrees with subtraction of the actual
continuous multiplier maps; the original completed element is unchanged. -/
theorem native_energyMulSmooth_sub
    (g : RiemannianMetric 3 M) (χ ψ : M → ℝ)
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hψ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ψ)
    (w : H1Zero g.leviCivitaData univ) :
    energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
      (fun x => χ x - ψ x) (hχ.sub hψ) w =
    energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) χ hχ w -
      energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) ψ hψ w := by
  induction w using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f =>
    simp only [energyMulSmooth_coe, ← Completion.coe_sub]
    congr 1
    apply Subtype.ext
    funext x
    exact sub_mul _ _ _

theorem native_energyMulSmooth_one (g : RiemannianMetric 3 M)
    (w : H1Zero g.leviCivitaData univ) :
    energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
      (fun _ => (1 : ℝ)) contMDiff_const w = w := by
  induction w using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f =>
    rw [energyMulSmooth_coe]
    congr 1
    apply Subtype.ext
    funext x
    exact one_mul _

/-- Restricted gradient energy of an actual multiplier is controlled by
the actual layer energy and layer L2 mass. Only values inside the stated
domain are used in the pointwise coefficient estimates. -/
theorem native_restricted_energyMulSmooth_sq_le
    (g : RiemannianMetric 3 M) (Ω Λ : Set M)
    (hΩ : MeasurableSet Ω) (hΛ : MeasurableSet Λ)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (A : ℝ) (hA : 0 ≤ A)
    (hv : ∀ x ∈ Ω, χ x ^ 2 ≤ Λ.indicator (fun _ => (1 : ℝ)) x)
    (hg : ∀ x ∈ Ω, g.inner x (g.leviCivitaData.gradient χ x)
      (g.leviCivitaData.gradient χ x) ≤ A * Λ.indicator (fun _ => (1 : ℝ)) x)
    (w : H1Zero g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g Ω
      (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) χ hχ w)
      (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) χ hχ w) ≤
      2 * nativeRestrictedGradientEnergy g Λ w w +
        2 * A * ‖nativeRestrictedL2CLM g Λ w‖ ^ 2 := by
  induction w using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih f =>
    rw [energyMulSmooth_coe, nativeRestrictedGradientEnergy_coe,
      nativeRestrictedGradientEnergy_coe, nativeRestrictedL2CLM_norm_sq_coe]
    let G : M → ℝ := fun x => g.inner x
      (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient f x)
    have hGn (x : M) : 0 ≤ G x := by
      by_cases hz : g.leviCivitaData.gradient f x = 0
      · simp [G, hz]
      · exact (g.pos x _ hz).le
    let H : M → ℝ := fun x => 2 * G x + 2 * A * f x ^ 2
    have hfi : Integrable (fun x => f x ^ 2) g.volumeMeasure := f.memLp.integrable_sq
    have hGi : Integrable G g.volumeMeasure := f.integrable_gradient f
    have hHi : Integrable H g.volumeMeasure := (hGi.const_mul _).add (hfi.const_mul _)
    have hHn (x : M) : 0 ≤ H x := by
      have hx := hGn x
      dsimp only [H]
      positivity
    have hpoint (x : M) (hx : x ∈ Ω) :
        g.inner x (g.leviCivitaData.gradient (f.mulSmooth χ hχ) x)
          (g.leviCivitaData.gradient (f.mulSmooth χ hχ) x) ≤ Λ.indicator H x := by
      have hm := gradient_mul_energy_le χ hχ f x
      have hgrad := mul_le_mul_of_nonneg_right (hv x hx) (hGn x)
      have hcoef := mul_le_mul_of_nonneg_left (hg x hx) (sq_nonneg (f x))
      by_cases hxΛ : x ∈ Λ
      · simp only [indicator_of_mem hxΛ, H, G] at hgrad hcoef ⊢
        nlinarith only [hm, hgrad, hcoef]
      · simp only [indicator_of_notMem hxΛ, H, G] at hgrad hcoef ⊢
        nlinarith only [hm, hgrad, hcoef]
    calc
      _ ≤ ∫ x in Ω, Λ.indicator H x ∂g.volumeMeasure :=
        setIntegral_mono_on ((f.mulSmooth χ hχ).integrable_gradient _).integrableOn
          (hHi.indicator hΛ).integrableOn hΩ hpoint
      _ ≤ ∫ x, Λ.indicator H x ∂g.volumeMeasure :=
        setIntegral_le_integral (hHi.indicator hΛ)
          (Eventually.of_forall fun x => by by_cases hx : x ∈ Λ <;> simp [hx, hHn])
      _ = _ := by
        rw [integral_indicator hΛ]
        dsimp only [H]
        rw [integral_add (hGi.integrableOn.const_mul _) (hfi.integrableOn.const_mul _),
          integral_const_mul, integral_const_mul]

/-- A zero diagonal of the same positive restricted-gradient form gives
zero pairing with every native H1 element. This is proved by the actual
quadratic discriminant, without assuming locality of gradients. -/
theorem nativeRestrictedGradientEnergy_zero_of_diagonal
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (v : H1Zero g.leviCivitaData univ)
    (hv : nativeRestrictedGradientEnergy g Ω v v = 0)
    (w : H1Zero g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g Ω v w = 0 := by
  let B := nativeRestrictedGradientEnergy g Ω
  have hd : discrim (B v v) (2 * B v w) (B w w) ≤ 0 := by
    apply discrim_le_zero
    intro t
    have hpos := nativeRestrictedGradientEnergy_nonneg g Ω (t • v + w)
    have heq : B (t • v + w) (t • v + w) =
        B v v * (t * t) + (2 * B v w) * t + B w w := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [nativeRestrictedGradientEnergy_symm g Ω w v]
      ring
    rw [← heq]
    exact hpos
  change B v v = 0 at hv
  rw [hv] at hd
  dsimp only [discrim] at hd
  change B v w = 0
  nlinarith only [hd, sq_nonneg (B v w)]

private theorem cauchySeq_of_norm_sub_sq_le
    {X : Type*} [NormedAddCommGroup X] (v : ℕ → X) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ m n, ‖v m - v n‖ ^ 2 ≤ ε m + ε n) : CauchySeq v := by
  apply Metric.cauchySeq_iff.mpr
  intro η hη
  have hevent : ∀ᶠ n in atTop, ε n < η ^ 2 / 2 :=
    hε.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < η ^ 2 / 2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  have hb := hbound m n
  have hm' := hN m hm
  have hn' := hN n hn
  nlinarith only [hb, hm', hn', hη, norm_nonneg (v m - v n)]

/-- Actual bounded smooth products converge in the original native L2
space to the literal exterior indicator product. The almost-everywhere
hypothesis concerns volume points only; no boundary restriction is made. -/
theorem native_energyMulSmooth_toL2_tendsto_indicator
    (g : RiemannianMetric 3 M) (Ω : Set M) (hΩ : MeasurableSet Ω)
    (χ : ℕ → M → ℝ)
    (hχ : ∀ n, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (χ n))
    (hrange : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hpoint : ∀ᵐ x ∂g.volumeMeasure, ∀ᶠ n in atTop,
      χ n x = Ω.indicator (fun _ => (1 : ℝ)) x)
    (w : H1Zero g.leviCivitaData univ) :
    let u := toL2 g.leviCivitaData univ w
    let uΩ := (MemLp.indicator hΩ (Lp.memLp u)).toLp (Ω.indicator u)
    Tendsto (fun n => toL2 g.leviCivitaData univ
      (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
        (χ n) (hχ n) w)) atTop (𝓝 uΩ) := by
  let u := toL2 g.leviCivitaData univ w
  let hU := MemLp.indicator hΩ (Lp.memLp u)
  let uΩ := hU.toLp (Ω.indicator u)
  let v := fun n => toL2 g.leviCivitaData univ
    (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
      (χ n) (hχ n) w)
  change Tendsto v atTop (𝓝 uΩ)
  have hnorm (n : ℕ) : ‖v n - uΩ‖ ^ 2 =
      ∫ x, (χ n x * u x - Ω.indicator u x) ^ 2 ∂g.volumeMeasure := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v n) uΩ,
      native_energyMulSmooth_toL2_ae g (χ n) (hχ n) w, hU.coeFn_toLp] with x hx hp hq
    rw [hx]
    change inner ℝ (v n x - uΩ x) (v n x - uΩ x) = _
    rw [hp, hq]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, u]
  have hi : Integrable (fun x => u x ^ 2) g.volumeMeasure := (Lp.memLp u).integrable_sq
  have hlim : Tendsto (fun n => ∫ x, (χ n x * u x - Ω.indicator u x) ^ 2 ∂g.volumeMeasure)
      atTop (𝓝 (∫ _x : M, (0 : ℝ) ∂g.volumeMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => u x ^ 2)
    · intro n
      exact (((hχ n).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u)).sub
        ((Lp.aestronglyMeasurable u).indicator hΩ)).pow 2
    · exact hi
    · intro n
      exact Eventually.of_forall fun x => by
        have hr := hrange n x
        have hcoeff : (χ n x - Ω.indicator (fun _ => (1 : ℝ)) x) ^ 2 ≤ 1 := by
          by_cases hx : x ∈ Ω
          · simp only [indicator_of_mem hx]
            nlinarith only [hr.1, hr.2]
          · simp only [indicator_of_notMem hx]
            nlinarith only [hr.1, hr.2]
        have heq : χ n x * u x - Ω.indicator u x =
            (χ n x - Ω.indicator (fun _ => (1 : ℝ)) x) * u x := by
          by_cases hx : x ∈ Ω <;> simp [hx, sub_mul]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), heq, mul_pow]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (u x))
    · filter_upwards [hpoint] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      rw [hn]
      by_cases hxΩ : x ∈ Ω <;> simp [hxΩ]
  have hsquare : Tendsto (fun n => ‖v n - uΩ‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnorm, integral_zero] using hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsquare.sqrt

/-- The actual exterior restriction is a contraction in the native
energy norm. This follows from the proved value and gradient identities:
the omitted interior part is orthogonal to the retained domain element. -/
theorem native_exterior_restriction_norm_le
    (g : RiemannianMetric 3 M) (Ω : Set M)
    (w : H1Zero g.leviCivitaData univ) (z : H1Zero g.leviCivitaData Ω)
    (hvalue : (toL2 g.leviCivitaData Ω z : M → ℝ) =ᵐ[g.volumeMeasure]
      Ω.indicator (toL2 g.leviCivitaData univ w))
    (hpair : ∀ W : H1Zero g.leviCivitaData univ,
      nativeRestrictedGradientEnergy g Ω W w = gradientEnergy g.leviCivitaData univ W
        (nativeDomainEnergyInclusion g Ω z)) :
    ‖z‖ ≤ ‖w‖ := by
  let v := nativeDomainEnergyInclusion g Ω z
  have hvalue' : (toL2 g.leviCivitaData univ v : M → ℝ) =ᵐ[g.volumeMeasure]
      Ω.indicator (toL2 g.leviCivitaData univ w) := by
    simpa only [v, nativeDomainEnergyInclusion_toL2] using hvalue
  have hL : inner ℝ (toL2 g.leviCivitaData univ w) (toL2 g.leviCivitaData univ v) =
      ‖toL2 g.leviCivitaData univ v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hvalue'] with x hx
    rw [hx]
    by_cases hxΩ : x ∈ Ω <;> simp [hxΩ]
  have hgrad : gradientEnergy g.leviCivitaData univ w v =
      gradientEnergy g.leviCivitaData univ v v := by
    calc
      _ = nativeRestrictedGradientEnergy g Ω w v :=
        (nativeRestrictedGradientEnergy_domain_right g Ω w z).symm
      _ = nativeRestrictedGradientEnergy g Ω v w := nativeRestrictedGradientEnergy_symm g Ω w v
      _ = _ := hpair v
  simp only [gradientEnergy_apply, hL, real_inner_self_eq_norm_sq] at hgrad
  have hinner : inner ℝ w v = ‖v‖ ^ 2 := by linarith only [hgrad]
  have hbound : ‖v‖ ^ 2 ≤ ‖w‖ * ‖v‖ := by
    rw [← hinner]
    exact real_inner_le_norm _ _
  have hn : ‖v‖ ≤ ‖w‖ := by
    by_cases hz : ‖v‖ = 0
    · simpa only [hz] using norm_nonneg w
    · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hz)
      exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [pow_two] using hbound)
  simpa only [v, norm_nativeDomainEnergyInclusion] using hn

namespace EuclideanSphereTrace

open SpherePolar SphereBoundaryLayer NativeChartSphereMetric

/- The pure coordinate and cutoff identities below retain the proof from
NativeChartBoundaryFlux. Keeping this private copy avoids importing its
unrelated global Sobolev regularity consumers into one-sided restriction. -/
section ActualChartCutoffGradient

open VectorField GreenParametrix
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem restriction_native_chart_gradient_pairing
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source)
    (hcoeff : gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    {f ψ : M → ℝ}
    (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (e x))
    (hψ : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) ψ (e x)) :
    g.inner (e x) (g.leviCivitaData.gradient ψ (e x)) (g.leviCivitaData.gradient f (e x)) =
      gE.inner x (gE.leviCivitaData.gradient (ψ ∘ e) x)
        (gE.leviCivitaData.gradient (f ∘ e) x) := by
  have hD : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  have hm := ChartOperatorTransfer.metric_pairing_of_coefficients g gE e x hcoeff
  rw [gE.leviCivitaData.gradient_comp_eq_mpullback g.leviCivitaData
    (hD.mdifferentiableAt hx) hψ hinv hm,
    gE.leviCivitaData.gradient_comp_eq_mpullback g.leviCivitaData
      (hD.mdifferentiableAt hx) hf hinv hm, hm]
  simp only [mpullback, hinv.self_apply_inverse]

/-- The actual original-manifold cutoff pairing, in the same chart and
metric, is the literal radial directional derivative. -/
private theorem restriction_chartExteriorCutoff_gradient_pairing
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hs : closedBall (0 : E) (r + ε) ⊆ e.source)
    {x : E} (hx : x ∈ e.source)
    (hcoeff : gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    {f : M → ℝ} (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (e x)) :
    g.inner (e x) (g.leviCivitaData.gradient (chartExteriorCutoff e r ε) (e x))
      (g.leviCivitaData.gradient f (e x)) =
      deriv (exteriorLayerProfile r ε) ‖x‖ * fderiv ℝ (f ∘ e) x (‖x‖⁻¹ • x) := by
  rw [restriction_native_chart_gradient_pairing g gE e he hei hx hcoeff hf
    ((chartExteriorCutoff_smooth e hei hr hε hs).mdifferentiable (by simp) (e x))]
  have hgerm : ((chartExteriorCutoff e r ε) ∘ e) =ᶠ[𝓝 x] exteriorSphereCutoff r ε := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact chartExteriorCutoff_comp_apply e r ε hy
  have hgrad : gE.leviCivitaData.gradient (((chartExteriorCutoff e r ε) ∘ e)) x =
      gE.leviCivitaData.gradient (exteriorSphereCutoff r ε) x := by
    unfold LeviCivitaData.gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq hgerm]
  rw [hgrad]
  exact native_exterior_cutoff_gradient_pairing gE hGauss hr hε (f ∘ e) x

end ActualChartCutoffGradient

private theorem exterior_cutoff_radial_derivative
    (r ε : ℝ) {x : E} (hx : x ≠ 0) :
    fderiv ℝ (exteriorSphereCutoff r ε) x (‖x‖⁻¹ • x) =
      deriv (exteriorLayerProfile r ε) ‖x‖ := by
  have hnorm : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have hd := ((exteriorLayerProfile_smooth r ε).differentiable (by simp) ‖x‖).hasDerivAt
  have h := hd.comp_hasFDerivAt x hnorm.hasFDerivAt
  change HasFDerivAt (exteriorSphereCutoff r ε) _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul, hnorm.fderiv_norm_self]
  field_simp [norm_ne_zero_iff.mpr hx]

private theorem chart_cutoff_gradient_zero_outside_ball
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    {r ε : ℝ} (hε : 0 < ε) (hs : closedBall (0 : E) (r + ε) ⊆ e.source)
    {y : M} (hy : y ∉ e '' closedBall (0 : E) (r + ε)) :
    g.leviCivitaData.gradient (chartExteriorCutoff e r ε) y = 0 := by
  have hsub : tsupport (coordinateExtension e (fun x => 1 - exteriorSphereCutoff r ε x)) ⊆
      e '' closedBall (0 : E) (r + ε) :=
    (tsupport_coordinateExtension_subset_image e (innerSphereCutoff_compactSupport hε)
      ((innerSphereCutoff_tsupport_subset hε).trans hs)).trans
        (image_mono (innerSphereCutoff_tsupport_subset hε))
  have hz := notMem_tsupport_iff_eventuallyEq.mp (fun ht => hy (hsub ht))
  have hχ : chartExteriorCutoff e r ε =ᶠ[𝓝 y] (fun _ : M => (1 : ℝ)) := by
    filter_upwards [hz] with z hz
    change 1 - coordinateExtension e (fun x => 1 - exteriorSphereCutoff r ε x) z = 1
    rw [hz, Pi.zero_apply, sub_zero]
  unfold LeviCivitaData.gradient
  rw [Poincare.mvfderiv_eq_of_eventuallyEq hχ]
  simp only [mvfderiv_const, map_zero]

/-- One fixed bound for the derivative of the literal transition profile.
It is chosen before the radius, thickness and native H1 element. -/
theorem exists_layer_profile_derivative_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℝ) {δ : ℝ}, 0 < δ → ∀ s : ℝ,
      (deriv (exteriorLayerProfile r δ) s) ^ 2 ≤ K * δ⁻¹ ^ 2 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    continuous_layerKernel.continuousOn
  let A := |C| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hkernel (t : ℝ) : |layerKernel t| ≤ A := by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · have hb : |layerKernel t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t ht
      exact hb.trans (by dsimp [A]; linarith only [le_abs_self C])
    · have hout : t ∉ Ioo (0 : ℝ) ((0 : ℝ) + 1) := by
        simpa only [zero_add] using fun h => ht ⟨h.1.le, h.2.le⟩
      have hz := exteriorLayerProfile_deriv_eq_zero_of_outside (by norm_num : (0 : ℝ) < 1) hout
      have heq : layerKernel t = 0 := by simpa only [exteriorLayerProfile_deriv,
        sub_zero, div_one] using hz
      rw [heq, abs_zero]
      exact hA.le
  refine ⟨A ^ 2, sq_pos_of_pos hA, ?_⟩
  intro r δ hδ s
  rw [exteriorLayerProfile_deriv, div_eq_mul_inv, mul_pow]
  have hsq : layerKernel ((s - r) / δ) ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hA.le).mpr (hkernel ((s - r) / δ))
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- The actual shifted native cutoff has order delta^-2 squared gradient
cost supported in the actual chart collar. This is proved by coordinate
transport and the Gauss radial identity, not supplied as boundary data. -/
theorem exists_shifted_chart_cutoff_gradient_bound
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    {a : ℝ} (ha : 0 < a)
    (hs : closedBall (0 : E) (2 * a) ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E) (2 * a),
      gE.euclideanCoefficients x = g.pullbackCoefficients e x) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → 2 * δ ≤ a → ∀ y : M,
      g.inner y (g.leviCivitaData.gradient (chartExteriorCutoff e (a + δ) δ) y)
        (g.leviCivitaData.gradient (chartExteriorCutoff e (a + δ) δ) y) ≤
        K * δ⁻¹ ^ 2 * (e '' sphereTraceAnnulus a (a + 2 * δ)).indicator
          (fun _ => (1 : ℝ)) y := by
  obtain ⟨K, hK, hderiv⟩ := exists_layer_profile_derivative_bound
  refine ⟨K, hK, ?_⟩
  intro δ hδ hδa y
  have hr : 0 < a + δ := add_pos ha hδ
  have houter : closedBall (0 : E) ((a + δ) + δ) ⊆ closedBall (0 : E) (2 * a) :=
    closedBall_subset_closedBall (by linarith only [hδa])
  have hsδ := houter.trans hs
  have hχ := chartExteriorCutoff_smooth e hei hr hδ hsδ
  by_cases hy : y ∈ e '' sphereTraceAnnulus a (a + 2 * δ)
  · rw [indicator_of_mem hy, mul_one]
    obtain ⟨x, hx, rfl⟩ := hy
    have hxb : x ∈ closedBall (0 : E) (2 * a) := by
      simp only [mem_closedBall, dist_zero_right]
      linarith only [hx.2, hδa]
    have hx0 : x ≠ 0 := by
      intro hz
      change a ≤ ‖x‖ ∧ ‖x‖ ≤ a + 2 * δ at hx
      rw [hz, norm_zero] at hx
      linarith only [hx.1, ha]
    rw [restriction_chartExteriorCutoff_gradient_pairing g gE e he hei hGauss hr hδ hsδ
      (hs hxb) (hcoeff x hxb) (hχ.mdifferentiable (by simp) (e x))]
    have hgerm : ((chartExteriorCutoff e (a + δ) δ) ∘ e) =ᶠ[𝓝 x]
        exteriorSphereCutoff (a + δ) δ := by
      filter_upwards [e.open_source.mem_nhds (hs hxb)] with z hz
      exact chartExteriorCutoff_comp_apply e (a + δ) δ hz
    rw [hgerm.fderiv_eq, exterior_cutoff_radial_derivative _ _ hx0, ← pow_two]
    exact hderiv (a + δ) hδ ‖x‖
  · rw [indicator_of_notMem hy, mul_zero]
    by_cases hyb : y ∈ e '' closedBall (0 : E) ((a + δ) + δ)
    · obtain ⟨x, hx, rfl⟩ := hyb
      have hout : ‖x‖ ∉ Ioo (a + δ) ((a + δ) + δ) := by
        intro hn
        apply hy
        exact ⟨x, ⟨by linarith only [hn.1, hδ], by linarith only [hn.2]⟩, rfl⟩
      rw [restriction_chartExteriorCutoff_gradient_pairing g gE e he hei hGauss hr hδ hsδ
        (hsδ hx) (hcoeff x (houter hx)) (hχ.mdifferentiable (by simp) (e x)),
        exteriorLayerProfile_deriv_eq_zero_of_outside hδ hout, zero_mul]
    · simp only [chart_cutoff_gradient_zero_outside_ball g e hδ hsδ hyb, map_zero, le_refl]

private theorem exterior_annulus_subset_source
    (e : OpenPartialHomeomorph E M) {a : ℝ}
    (hs : closedBall (0 : E) (2 * a) ⊆ e.source) :
    sphereTraceAnnulus a (2 * a) ⊆ e.source := by
  intro x hx
  exact hs (by simpa only [mem_closedBall, dist_zero_right] using hx.2)

private theorem exterior_annulus_coefficients
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
    (e : OpenPartialHomeomorph E M) {a : ℝ}
    (hcoeff : ∀ x ∈ closedBall (0 : E) (2 * a),
      gE.euclideanCoefficients x = g.pullbackCoefficients e x) :
    ∀ x ∈ sphereTraceAnnulus a (2 * a),
      gE.euclideanCoefficients x = g.pullbackCoefficients e x := by
  intro x hx
  exact hcoeff x (by simpa only [mem_closedBall, dist_zero_right] using hx.2)

private theorem shifted_collar_measurable
    (e : OpenPartialHomeomorph E M) {a δ : ℝ}
    (hs : closedBall (0 : E) (2 * a) ⊆ e.source) (hδa : 2 * δ ≤ a) :
    MeasurableSet (e '' sphereTraceAnnulus a (a + 2 * δ)) := by
  have hsub : sphereTraceAnnulus a (a + 2 * δ) ⊆ e.source := by
    intro x hx
    apply hs
    simp only [mem_closedBall, dist_zero_right]
    linarith only [hx.2, hδa]
  exact ((isCompact_sphereTraceAnnulus a (a + 2 * δ)).image_of_continuousOn
    (e.continuousOn.mono hsub)).measurableSet

/-- A named actual shifted cutoff multiplier on the original completion. -/
def nativeShiftedExteriorMultiplier
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a : ℝ} (ha : 0 < a) (hs : closedBall (0 : E) (2 * a) ⊆ e.source)
    (δ : ℝ) (hδ : 0 < δ) (hδa : 2 * δ ≤ a) :
    H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ :=
  energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
    (chartExteriorCutoff e (a + δ) δ)
    (chartExteriorCutoff_smooth e hei (add_pos ha hδ) hδ
      ((closedBall_subset_closedBall (by linarith only [hδa])).trans hs))

section ExteriorCompletion

variable (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
  (e : OpenPartialHomeomorph E M)
  (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
  {a A : ℝ} (ha : 0 < a)
  (hs : closedBall (0 : E) (2 * a) ⊆ e.source)
  (hcoeff : ∀ x ∈ closedBall (0 : E) (2 * a),
    gE.euclideanCoefficients x = g.pullbackCoefficients e x)
  (hA : 0 ≤ A)
  (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (a • (θ : E)) ≤ A)

local notation "hAnn" => exterior_annulus_subset_source e hs
local notation "hCoeffAnn" => exterior_annulus_coefficients g gE e hcoeff
local notation "hrInner" => (And.intro le_rfl (le_of_lt (lt_two_mul_self ha)))
local notation "habInner" => (lt_two_mul_self ha)
local notation "hθInner" => (fun θ : S => radial_mem_sphereTraceAnnulus ha hrInner θ)
local notation "T" => nativePhysicalSphereTraceCLM g gE e he hei ha habInner hrInner hAnn hA
  (fun θ => hCoeffAnn _ (hθInner θ)) (fun θ => hGauss (a • (θ : E))) hρ

/-- The concrete supported products of a zero canonical-trace element
are Cauchy in the original global H1 norm. All cutoff costs are proved
from the actual metric, trace and shrinking-collar energy. -/
theorem native_shifted_cutoff_products_cauchy
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδa : ∀ n, 2 * δ n ≤ a) (hδ : Tendsto δ atTop (𝓝 0))
    (w : H1Zero g.leviCivitaData univ) (hw : T w = 0) :
    CauchySeq (fun n => nativeShiftedExteriorMultiplier g e hei ha hs
      (δ n) (hδpos n) (hδa n) w) := by
  let L := fun n => e '' sphereTraceAnnulus a (a + 2 * δ n)
  let χ := fun n => chartExteriorCutoff e (a + δ n) (δ n)
  have hχ (n : ℕ) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (χ n) :=
    chartExteriorCutoff_smooth e hei (add_pos ha (hδpos n)) (hδpos n)
      ((closedBall_subset_closedBall (by linarith only [hδa n])).trans hs)
  let v := fun n => energyMulSmooth g.leviCivitaData univ
    (by simpa using isCompact_univ) (χ n) (hχ n) w
  change CauchySeq v
  have hLm (n : ℕ) : MeasurableSet (L n) := shifted_collar_measurable e hs (hδa n)
  obtain ⟨K, hK, hKbound⟩ := exists_shifted_chart_cutoff_gradient_bound
    g gE e he hei hGauss ha hs hcoeff
  let ε := fun n => ‖nativeRestrictedL2CLM g (L n) w‖ ^ 2 +
    4 * K * ((δ n)⁻¹ ^ 2 * ‖nativeRestrictedL2CLM g (L n) w‖ ^ 2) +
    2 * nativeRestrictedGradientEnergy g (L n) w w
  have hmass := nativeRestrictedL2CLM_norm_sq_tendsto_zero g L hLm
    (native_chart_collar_eventually_avoids_ae g e he hei ha hAnn δ hδa hδ) w
  have hscaled := native_zero_trace_scaled_collar_mass_tendsto_zero
    g gE e he hei ha hAnn hCoeffAnn (fun x _ => hGauss x) hA hρ
    δ hδpos hδa hδ w hw
  have hgradient := native_chart_collar_gradient_energy_tendsto_zero
    g e he hei ha hAnn δ hδa hδ w
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, L, mul_zero, add_zero] using
      (hmass.add (hscaled.const_mul (4 * K))).add (hgradient.const_mul 2)
  apply cauchySeq_of_norm_sub_sq_le v ε hε
  intro m n
  have hsδ (i : ℕ) : closedBall (0 : E) (a + 2 * δ i) ⊆ e.source :=
    (closedBall_subset_closedBall (by linarith only [hδa i])).trans hs
  have hvalue (x : M) : (χ m x - χ n x) ^ 2 ≤
      (L m).indicator (fun _ => (1 : ℝ)) x + (L n).indicator (fun _ => (1 : ℝ)) x :=
    shifted_chartExteriorCutoff_sub_sq_le e (hδpos m) (hδpos n) (hsδ m) (hsδ n) x
  have hgrad (x : M) :
      g.inner x (g.leviCivitaData.gradient (fun y => χ m y - χ n y) x)
        (g.leviCivitaData.gradient (fun y => χ m y - χ n y) x) ≤
      (2 * K * (δ m)⁻¹ ^ 2) * (L m).indicator (fun _ => (1 : ℝ)) x +
      (2 * K * (δ n)⁻¹ ^ 2) * (L n).indicator (fun _ => (1 : ℝ)) x := by
    calc
      _ ≤ 2 * g.inner x (g.leviCivitaData.gradient (χ m) x)
          (g.leviCivitaData.gradient (χ m) x) +
          2 * g.inner x (g.leviCivitaData.gradient (χ n) x)
          (g.leviCivitaData.gradient (χ n) x) :=
        native_gradient_sub_sq_le g (hχ m) (hχ n) x
      _ ≤ 2 * (K * (δ m)⁻¹ ^ 2 * (L m).indicator (fun _ => (1 : ℝ)) x) +
          2 * (K * (δ n)⁻¹ ^ 2 * (L n).indicator (fun _ => (1 : ℝ)) x) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hKbound (δ m) (hδpos m) (hδa m) x) (by norm_num))
          (mul_le_mul_of_nonneg_left (hKbound (δ n) (hδpos n) (hδa n) x) (by norm_num))
      _ = _ := by ring
  have hb := native_energyMulSmooth_two_domain_norm_sq_le g (L m) (L n) (hLm m) (hLm n)
    (fun x => χ m x - χ n x) ((hχ m).sub (hχ n))
    (2 * K * (δ m)⁻¹ ^ 2) (2 * K * (δ n)⁻¹ ^ 2) hvalue hgrad w
  rw [native_energyMulSmooth_sub g (χ m) (χ n) (hχ m) (hχ n) w] at hb
  calc
    ‖v m - v n‖ ^ 2 ≤ _ := hb
    _ = ε m + ε n := by dsimp only [ε]; ring

/-- Inside the exterior domain the multiplier residual has vanishing
actual gradient energy. The nonzero interior part of the original
global element is correctly excluded from this restricted estimate. -/
theorem native_shifted_cutoff_residual_energy_tendsto_zero
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδa : ∀ n, 2 * δ n ≤ a) (hδ : Tendsto δ atTop (𝓝 0))
    (w : H1Zero g.leviCivitaData univ) (hw : T w = 0) :
    Tendsto (fun n => nativeRestrictedGradientEnergy g (e '' closedBall (0 : E) a)ᶜ
      (w - nativeShiftedExteriorMultiplier g e hei ha hs (δ n) (hδpos n) (hδa n) w)
      (w - nativeShiftedExteriorMultiplier g e hei ha hs (δ n) (hδpos n) (hδa n) w))
      atTop (𝓝 0) := by
  let Ω := (e '' closedBall (0 : E) a)ᶜ
  let L := fun n => e '' sphereTraceAnnulus a (a + 2 * δ n)
  let χ := fun n => chartExteriorCutoff e (a + δ n) (δ n)
  have hχ (n : ℕ) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (χ n) :=
    chartExteriorCutoff_smooth e hei (add_pos ha (hδpos n)) (hδpos n)
      ((closedBall_subset_closedBall (by linarith only [hδa n])).trans hs)
  have hsδ (n : ℕ) : closedBall (0 : E) (a + 2 * δ n) ⊆ e.source :=
    (closedBall_subset_closedBall (by linarith only [hδa n])).trans hs
  have hΩ : MeasurableSet Ω :=
    ((isCompact_closedBall (0 : E) a).image_of_continuousOn
      (e.continuousOn.mono ((closedBall_subset_closedBall (by linarith only [ha])).trans hs))).measurableSet.compl
  have hLm (n : ℕ) : MeasurableSet (L n) := shifted_collar_measurable e hs (hδa n)
  obtain ⟨K, hK, hKbound⟩ := exists_shifted_chart_cutoff_gradient_bound
    g gE e he hei hGauss ha hs hcoeff
  have hscaled := native_zero_trace_scaled_collar_mass_tendsto_zero
    g gE e he hei ha hAnn hCoeffAnn (fun x _ => hGauss x) hA hρ
    δ hδpos hδa hδ w hw
  have hgradient := native_chart_collar_gradient_energy_tendsto_zero
    g e he hei ha hAnn δ hδa hδ w
  have hupper : Tendsto (fun n => 2 * nativeRestrictedGradientEnergy g (L n) w w +
      4 * K * ((δ n)⁻¹ ^ 2 * ‖nativeRestrictedL2CLM g (L n) w‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [L, mul_zero, add_zero] using
      (hgradient.const_mul 2).add (hscaled.const_mul (4 * K))
  apply squeeze_zero (fun n => nativeRestrictedGradientEnergy_nonneg g Ω _)
    (fun n => ?_) hupper
  have hvalue (x : M) (hx : x ∈ Ω) :
      (1 - χ n x) ^ 2 ≤ (L n).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hxL : x ∈ L n
    · rw [indicator_of_mem hxL]
      have hr := chartExteriorCutoff_range e (a + δ n) (δ n) x
      change (1 - chartExteriorCutoff e (a + δ n) (δ n) x) ^ 2 ≤ 1
      nlinarith only [hr.1, hr.2]
    · have hv := shifted_chartExteriorCutoff_eq_indicator_off_collar e
        (hδpos n) (hsδ n) hxL
      change χ n x = Ω.indicator (fun _ => (1 : ℝ)) x at hv
      rw [hv, indicator_of_mem hx, sub_self, zero_pow (by decide : 2 ≠ 0),
        indicator_of_notMem hxL]
  have hgrad (x : M) (_hx : x ∈ Ω) :
      g.inner x (g.leviCivitaData.gradient (fun y => 1 - χ n y) x)
        (g.leviCivitaData.gradient (fun y => 1 - χ n y) x) ≤
      (2 * K * (δ n)⁻¹ ^ 2) * (L n).indicator (fun _ => (1 : ℝ)) x := by
    have hz : g.leviCivitaData.gradient (fun _ : M => (1 : ℝ)) x = 0 := by
      simp only [LeviCivitaData.gradient, mvfderiv_const, map_zero]
    have hb := native_gradient_sub_sq_le g
      (χ := fun _ : M => (1 : ℝ)) contMDiff_const (hχ n) x
    rw [hz, map_zero, mul_zero, zero_add] at hb
    calc
      _ ≤ 2 * g.inner x (g.leviCivitaData.gradient (χ n) x)
          (g.leviCivitaData.gradient (χ n) x) := hb
      _ ≤ 2 * (K * (δ n)⁻¹ ^ 2 * (L n).indicator (fun _ => (1 : ℝ)) x) :=
        mul_le_mul_of_nonneg_left (hKbound (δ n) (hδpos n) (hδa n) x) (by norm_num)
      _ = _ := by ring
  have hb := native_restricted_energyMulSmooth_sq_le g Ω (L n) hΩ (hLm n)
    (fun x => 1 - χ n x) (contMDiff_const.sub (hχ n))
    (2 * K * (δ n)⁻¹ ^ 2) (by positivity) hvalue hgrad w
  rw [native_energyMulSmooth_sub g (fun _ : M => (1 : ℝ)) (χ n)
    contMDiff_const (hχ n) w, native_energyMulSmooth_one] at hb
  calc
    _ ≤ _ := hb
    _ = _ := by ring

/-- The actual one-sided restriction producer. The returned domain
element represents exactly the original field multiplied by the exterior
indicator. Its restricted-gradient locality is also proved, not inferred
from that value identity alone. -/
theorem exists_native_zero_trace_exterior_restriction_of_sequence
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδa : ∀ n, 2 * δ n ≤ a) (hδ : Tendsto δ atTop (𝓝 0))
    (w : H1Zero g.leviCivitaData univ) (hw : T w = 0) :
    ∃ z : H1Zero g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ,
      (toL2 g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ z : M → ℝ) =ᵐ[g.volumeMeasure]
        (e '' closedBall (0 : E) a)ᶜ.indicator (toL2 g.leviCivitaData univ w) ∧
      nativeRestrictedGradientEnergy g (e '' closedBall (0 : E) a)ᶜ
        (w - nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z)
        (w - nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z) = 0 ∧
      ∀ W : H1Zero g.leviCivitaData univ,
        nativeRestrictedGradientEnergy g (e '' closedBall (0 : E) a)ᶜ W w =
          gradientEnergy g.leviCivitaData univ W
            (nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z) := by
  let Ω := (e '' closedBall (0 : E) a)ᶜ
  let χ := fun n => chartExteriorCutoff e (a + δ n) (δ n)
  have hχ (n : ℕ) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (χ n) :=
    chartExteriorCutoff_smooth e hei (add_pos ha (hδpos n)) (hδpos n)
      ((closedBall_subset_closedBall (by linarith only [hδa n])).trans hs)
  let v := fun n => energyMulSmooth g.leviCivitaData univ
    (by simpa using isCompact_univ) (χ n) (hχ n) w
  have hΩ : MeasurableSet Ω :=
    ((isCompact_closedBall (0 : E) a).image_of_continuousOn
      (e.continuousOn.mono ((closedBall_subset_closedBall (by linarith only [ha])).trans hs))).measurableSet.compl
  have hsδ (n : ℕ) : closedBall (0 : E) (a + 2 * δ n) ⊆ e.source :=
    (closedBall_subset_closedBall (by linarith only [hδa n])).trans hs
  have hc : CauchySeq v := native_shifted_cutoff_products_cauchy
    g gE e he hei hGauss ha hs hcoeff hA hρ δ hδpos hδa hδ w hw
  obtain ⟨vLimit, hvLimit⟩ := cauchySeq_tendsto_of_complete hc
  have hsupported (n : ℕ) : v n ∈ Set.range (nativeDomainEnergyInclusion g Ω) :=
    native_energyMulSmooth_mem_domain_range g Ω (χ n) (hχ n)
      (shifted_chartExteriorCutoff_tsupport_subset e (hδpos n) (hsδ n)) w
  obtain ⟨z, hz⟩ := native_domain_range_of_tendsto g Ω v hsupported vLimit hvLimit
  have hpoint : ∀ᵐ x ∂g.volumeMeasure, ∀ᶠ n in atTop,
      χ n x = Ω.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [native_chart_collar_eventually_avoids_ae g e he hei ha hAnn δ hδa hδ] with x hx
    filter_upwards [hx] with n hn
    exact shifted_chartExteriorCutoff_eq_indicator_off_collar e (hδpos n) (hsδ n) hn
  let u := toL2 g.leviCivitaData univ w
  let hU := MemLp.indicator hΩ (Lp.memLp u)
  let uΩ := hU.toLp (Ω.indicator u)
  have hl2 : Tendsto (fun n => toL2 g.leviCivitaData univ (v n)) atTop (𝓝 uΩ) :=
    native_energyMulSmooth_toL2_tendsto_indicator g Ω hΩ χ hχ
      (fun n x => chartExteriorCutoff_range e (a + δ n) (δ n) x) hpoint w
  have hl2' : Tendsto (fun n => toL2 g.leviCivitaData univ (v n)) atTop
      (𝓝 (toL2 g.leviCivitaData univ vLimit)) :=
    (toL2 g.leviCivitaData univ).continuous.continuousAt.tendsto.comp hvLimit
  have heq : toL2 g.leviCivitaData univ vLimit = uΩ := tendsto_nhds_unique hl2' hl2
  have hvalue : (toL2 g.leviCivitaData Ω z : M → ℝ) =ᵐ[g.volumeMeasure] Ω.indicator u := by
    rw [← nativeDomainEnergyInclusion_toL2 g Ω z, hz, heq]
    exact hU.coeFn_toLp
  have hresidual : nativeRestrictedGradientEnergy g Ω
      (w - nativeDomainEnergyInclusion g Ω z) (w - nativeDomainEnergyInclusion g Ω z) = 0 := by
    have hzero := native_shifted_cutoff_residual_energy_tendsto_zero
      g gE e he hei hGauss ha hs hcoeff hA hρ δ hδpos hδa hδ w hw
    have hcontinuous : Continuous (fun q : H1Zero g.leviCivitaData univ =>
        nativeRestrictedGradientEnergy g Ω (w - q) (w - q)) := by fun_prop
    have ht := hcontinuous.continuousAt.tendsto.comp hvLimit
    rw [← hz] at ht
    exact tendsto_nhds_unique ht hzero
  refine ⟨z, hvalue, hresidual, ?_⟩
  intro W
  have hzero := nativeRestrictedGradientEnergy_zero_of_diagonal g Ω
    (w - nativeDomainEnergyInclusion g Ω z) hresidual W
  rw [nativeRestrictedGradientEnergy_symm g Ω _ W, map_sub,
    nativeRestrictedGradientEnergy_domain_right] at hzero
  exact sub_eq_zero.mp hzero

/-- A fixed positive null thickness sequence makes the restriction
producer unconditional on any externally supplied approximation sequence. -/
theorem exists_native_zero_trace_exterior_restriction
    (w : H1Zero g.leviCivitaData univ) (hw : T w = 0) :
    ∃ z : H1Zero g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ,
      (toL2 g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ z : M → ℝ) =ᵐ[g.volumeMeasure]
        (e '' closedBall (0 : E) a)ᶜ.indicator (toL2 g.leviCivitaData univ w) ∧
      nativeRestrictedGradientEnergy g (e '' closedBall (0 : E) a)ᶜ
        (w - nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z)
        (w - nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z) = 0 ∧
      ∀ W : H1Zero g.leviCivitaData univ,
        nativeRestrictedGradientEnergy g (e '' closedBall (0 : E) a)ᶜ W w =
          gradientEnergy g.leviCivitaData univ W
            (nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z) := by
  let δ := fun n : ℕ => (a / 4) * (1 / ((n : ℝ) + 1))
  have hδpos (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδa (n : ℕ) : 2 * δ n ≤ a := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      linarith only [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    have hi : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr (by simpa only [one_mul] using hn)
    have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ a / 4 by positivity)
    dsimp only [δ]
    nlinarith only [hm, ha]
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (a / 4)
  exact exists_native_zero_trace_exterior_restriction_of_sequence
    g gE e he hei hGauss ha hs hcoeff hA hρ δ hδpos hδa hδ w hw

/-- The domain representative of the actual indicator restriction is
unique in the original completion, not an independently selected solution. -/
theorem exists_unique_native_zero_trace_exterior_value
    (w : H1Zero g.leviCivitaData univ) (hw : T w = 0) :
    ∃! z : H1Zero g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ,
      (toL2 g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ z : M → ℝ) =ᵐ[g.volumeMeasure]
        (e '' closedBall (0 : E) a)ᶜ.indicator (toL2 g.leviCivitaData univ w) := by
  obtain ⟨z, hz, _, _⟩ := exists_native_zero_trace_exterior_restriction
    g gE e he hei hGauss ha hs hcoeff hA hρ w hw
  refine ⟨z, hz, ?_⟩
  intro y hy
  apply toL2_injective
  exact Lp.ext (hy.trans hz.symm)

/-- The one-sided producer with its sharp explicit continuity constant 1. -/
theorem exists_native_zero_trace_exterior_restriction_bounded
    (w : H1Zero g.leviCivitaData univ) (hw : T w = 0) :
    ∃ z : H1Zero g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ,
      (toL2 g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ z : M → ℝ) =ᵐ[g.volumeMeasure]
        (e '' closedBall (0 : E) a)ᶜ.indicator (toL2 g.leviCivitaData univ w) ∧
      nativeRestrictedGradientEnergy g (e '' closedBall (0 : E) a)ᶜ
        (w - nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z)
        (w - nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z) = 0 ∧
      (∀ W : H1Zero g.leviCivitaData univ,
        nativeRestrictedGradientEnergy g (e '' closedBall (0 : E) a)ᶜ W w =
          gradientEnergy g.leviCivitaData univ W
            (nativeDomainEnergyInclusion g (e '' closedBall (0 : E) a)ᶜ z)) ∧
      ‖z‖ ≤ ‖w‖ := by
  obtain ⟨z, hz, hres, hpair⟩ := exists_native_zero_trace_exterior_restriction
    g gE e he hei hGauss ha hs hcoeff hA hρ w hw
  exact ⟨z, hz, hres, hpair, native_exterior_restriction_norm_le g _ w z hz hpair⟩

/-- The restriction is linear on the kernel of the genuine physical
trace. Linearity is proved through the injective original L2 realization
and the already constructed literal indicator value. -/
def nativeZeroTraceExteriorRestrictionLinear :
    (T).ker →ₗ[ℝ] H1Zero g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ := by
  let Ω := (e '' closedBall (0 : E) a)ᶜ
  let f : (T).ker → H1Zero g.leviCivitaData Ω := fun w =>
    (exists_native_zero_trace_exterior_restriction_bounded
      g gE e he hei hGauss ha hs hcoeff hA hρ w.val w.property).choose
  have hf (w : (T).ker) : (toL2 g.leviCivitaData Ω (f w) : M → ℝ) =ᵐ[g.volumeMeasure]
      Ω.indicator (toL2 g.leviCivitaData univ w.val) :=
    (exists_native_zero_trace_exterior_restriction_bounded
      g gE e he hei hGauss ha hs hcoeff hA hρ w.val w.property).choose_spec.1
  refine { toFun := f, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    apply toL2_injective
    rw [map_add]
    apply Lp.ext
    filter_upwards [hf (v + w), hf v, hf w,
      Lp.coeFn_add (toL2 g.leviCivitaData Ω (f v)) (toL2 g.leviCivitaData Ω (f w)),
      Lp.coeFn_add (toL2 g.leviCivitaData univ v.val) (toL2 g.leviCivitaData univ w.val)]
      with x hsum hv hw hout hsrc
    rw [hsum, hout]
    simp only [Pi.add_apply]
    rw [hv, hw]
    change Ω.indicator (toL2 g.leviCivitaData univ (v.val + w.val)) x = _
    rw [map_add]
    by_cases hx : x ∈ Ω
    · simpa only [indicator_of_mem hx, Pi.add_apply] using hsrc
    · simp only [indicator_of_notMem hx, zero_add]
  · intro c w
    apply toL2_injective
    rw [map_smul]
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [hf (c • w), hf w,
      Lp.coeFn_smul c (toL2 g.leviCivitaData Ω (f w)),
      Lp.coeFn_smul c (toL2 g.leviCivitaData univ w.val)] with x hsmul hw hout hsrc
    rw [hsmul, hout]
    simp only [Pi.smul_apply]
    rw [hw]
    change Ω.indicator (toL2 g.leviCivitaData univ (c • w.val)) x = _
    rw [map_smul]
    by_cases hx : x ∈ Ω
    · simpa only [indicator_of_mem hx, Pi.smul_apply] using hsrc
    · simp only [indicator_of_notMem hx, smul_zero]

/-- A genuine continuous linear one-sided restriction with explicit
operator-norm bound 1, defined only on the actual zero-trace data space. -/
def nativeZeroTraceExteriorRestrictionCLM :
    (T).ker →L[ℝ] H1Zero g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ :=
  (nativeZeroTraceExteriorRestrictionLinear g gE e he hei hGauss ha hs hcoeff hA hρ).mkContinuous 1
    (fun w => by
      change ‖(exists_native_zero_trace_exterior_restriction_bounded
        g gE e he hei hGauss ha hs hcoeff hA hρ w.val w.property).choose‖ ≤ 1 * ‖w‖
      rw [one_mul]
      exact (exists_native_zero_trace_exterior_restriction_bounded
        g gE e he hei hGauss ha hs hcoeff hA hρ w.val w.property).choose_spec.2.2.2)

theorem nativeZeroTraceExteriorRestrictionCLM_norm_le :
    ‖nativeZeroTraceExteriorRestrictionCLM g gE e he hei hGauss ha hs hcoeff hA hρ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  change ‖(exists_native_zero_trace_exterior_restriction_bounded
    g gE e he hei hGauss ha hs hcoeff hA hρ w.val w.property).choose‖ ≤ 1 * ‖w‖
  rw [one_mul]
  exact (exists_native_zero_trace_exterior_restriction_bounded
    g gE e he hei hGauss ha hs hcoeff hA hρ w.val w.property).choose_spec.2.2.2

theorem nativeZeroTraceExteriorRestrictionCLM_toL2_ae (w : (T).ker) :
    (toL2 g.leviCivitaData (e '' closedBall (0 : E) a)ᶜ
      (nativeZeroTraceExteriorRestrictionCLM g gE e he hei hGauss ha hs hcoeff hA hρ w) : M → ℝ)
      =ᵐ[g.volumeMeasure] (e '' closedBall (0 : E) a)ᶜ.indicator
        (toL2 g.leviCivitaData univ w.val) :=
  (exists_native_zero_trace_exterior_restriction_bounded
    g gE e he hei hGauss ha hs hcoeff hA hρ w.val w.property).choose_spec.1

theorem nativeZeroTraceExteriorRestrictionCLM_gradient_pairing (w : (T).ker)
    (W : H1Zero g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g (e '' closedBall (0 : E) a)ᶜ W w.val =
      gradientEnergy g.leviCivitaData univ W (nativeDomainEnergyInclusion g
        (e '' closedBall (0 : E) a)ᶜ
        (nativeZeroTraceExteriorRestrictionCLM g gE e he hei hGauss ha hs hcoeff hA hρ w)) :=
  (exists_native_zero_trace_exterior_restriction_bounded
    g gE e he hei hGauss ha hs hcoeff hA hρ w.val w.property).choose_spec.2.2.1 W

end ExteriorCompletion

end EuclideanSphereTrace

#print axioms native_energyMulSmooth_two_domain_norm_sq_le
#print axioms native_energyMulSmooth_sub
#print axioms native_restricted_energyMulSmooth_sq_le
#print axioms nativeRestrictedGradientEnergy_zero_of_diagonal
#print axioms native_energyMulSmooth_toL2_tendsto_indicator
#print axioms native_exterior_restriction_norm_le
#print axioms EuclideanSphereTrace.exists_layer_profile_derivative_bound
#print axioms EuclideanSphereTrace.exists_shifted_chart_cutoff_gradient_bound
#print axioms EuclideanSphereTrace.native_shifted_cutoff_products_cauchy
#print axioms EuclideanSphereTrace.native_shifted_cutoff_residual_energy_tendsto_zero
#print axioms EuclideanSphereTrace.exists_native_zero_trace_exterior_restriction
#print axioms EuclideanSphereTrace.exists_unique_native_zero_trace_exterior_value
#print axioms EuclideanSphereTrace.exists_native_zero_trace_exterior_restriction_bounded
#print axioms EuclideanSphereTrace.nativeZeroTraceExteriorRestrictionCLM
#print axioms EuclideanSphereTrace.nativeZeroTraceExteriorRestrictionCLM_norm_le
#print axioms EuclideanSphereTrace.nativeZeroTraceExteriorRestrictionCLM_toL2_ae
#print axioms EuclideanSphereTrace.nativeZeroTraceExteriorRestrictionCLM_gradient_pairing

end Yamabe3.Analysis
