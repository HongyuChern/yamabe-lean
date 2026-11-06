import Yamabe3.Analysis.NativeDomainEnergyInclusionCore
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.WeakDirichlet
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The native gradient energy restricted to an actual domain

The form is first defined by the native integral on global smooth energy
tests and then extended in both arguments to the genuine H1 completion.
Its norm bound follows from positivity, the real quadratic discriminant,
and the actual global energy norm. If the second argument is in H1-zero
of the domain, the restricted form agrees with the global gradient form.
This provides the domain integral needed for a later conormal functional;
no boundary flux or normal trace is asserted by this file.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff Bundle InnerProductSpace

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

private theorem bilinear_norm_le_of_nonnegative_quadratic_bound
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x, 0 ≤ B x x)
    (hupper : ∀ x, B x x ≤ ‖x‖ ^ 2) (x y : E) :
    ‖B x y‖ ≤ ‖x‖ * ‖y‖ := by
  have hd : discrim (B x x) (2 * B x y) (B y y) ≤ 0 := by
    apply discrim_le_zero
    intro t
    have he : B (t • x + y) (t • x + y) =
        B x x * (t * t) + (2 * B x y) * t + B y y := by
      simp only [map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [hsym y x]
      ring
    rw [← he]
    exact hpos _
  have hsq : (B x y) ^ 2 ≤ B x x * B y y := by
    dsimp only [discrim] at hd
    nlinarith only [hd]
  have hm : B x x * B y y ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 :=
    mul_le_mul (hupper x) (hupper y) (hpos y) (sq_nonneg ‖x‖)
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  simpa only [← sq, Real.norm_eq_abs, sq_abs, mul_pow] using hsq.trans hm

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def restrictedGradientH1NormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] restrictedGradientH1NormedSpace

private def restrictedGradientTest (g : RiemannianMetric 3 M) (Ω : Set M)
    (f h : EnergyTest g.leviCivitaData univ) : ℝ :=
  ∫ x in Ω, g.inner x (g.leviCivitaData.gradient f x)
    (g.leviCivitaData.gradient h x) ∂g.volumeMeasure

private theorem restrictedGradientTest_symm (g : RiemannianMetric 3 M) (Ω : Set M)
    (f h : EnergyTest g.leviCivitaData univ) :
    restrictedGradientTest g Ω f h = restrictedGradientTest g Ω h f := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change inner ℝ (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient h x) =
      inner ℝ (g.leviCivitaData.gradient h x) (g.leviCivitaData.gradient f x)
    exact real_inner_comm _ _

private theorem restrictedGradientTest_add_left (g : RiemannianMetric 3 M) (Ω : Set M)
    (f h k : EnergyTest g.leviCivitaData univ) :
    restrictedGradientTest g Ω (f + h) k =
      restrictedGradientTest g Ω f k + restrictedGradientTest g Ω h k := by
  have hgrad (x : M) : g.leviCivitaData.gradient (fun y => f y + h y) x =
      g.leviCivitaData.gradient f x + g.leviCivitaData.gradient h x :=
    g.leviCivitaData.gradient_add ((f.smooth x).mdifferentiableAt (by simp))
      ((h.smooth x).mdifferentiableAt (by simp))
  simp only [restrictedGradientTest, EnergyTest.coe_add, hgrad, map_add, add_apply,
    integral_add (f.integrable_gradient k).integrableOn (h.integrable_gradient k).integrableOn]

private theorem restrictedGradientTest_smul_left (g : RiemannianMetric 3 M) (Ω : Set M)
    (c : ℝ) (f h : EnergyTest g.leviCivitaData univ) :
    restrictedGradientTest g Ω (c • f) h = c * restrictedGradientTest g Ω f h := by
  have hgrad (x : M) : g.leviCivitaData.gradient (fun y => c * f y) x =
      c • g.leviCivitaData.gradient f x := by
    apply (g.inner_isInvertible x).injective
    ext v
    simp only [g.leviCivitaData.inner_gradient, mvfderiv_const_mul,
      map_smul, smul_apply, smul_eq_mul]
  simp only [restrictedGradientTest, EnergyTest.coe_smul, hgrad, map_smul,
    smul_apply, smul_eq_mul, integral_const_mul]

private def restrictedGradientTestBilinear (g : RiemannianMetric 3 M) (Ω : Set M) :
    EnergyTest g.leviCivitaData univ →ₗ[ℝ]
      EnergyTest g.leviCivitaData univ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (restrictedGradientTest g Ω)
    (restrictedGradientTest_add_left g Ω) (restrictedGradientTest_smul_left g Ω)
    (fun f h k => by
      rw [restrictedGradientTest_symm g Ω, restrictedGradientTest_add_left,
        restrictedGradientTest_symm g Ω h f, restrictedGradientTest_symm g Ω k f])
    (fun c f h => by
      change restrictedGradientTest g Ω f (c • h) = c • restrictedGradientTest g Ω f h
      rw [restrictedGradientTest_symm g Ω, restrictedGradientTest_smul_left,
        restrictedGradientTest_symm g Ω h f]
      rfl)

private theorem restrictedGradientTest_nonneg (g : RiemannianMetric 3 M) (Ω : Set M)
    (f : EnergyTest g.leviCivitaData univ) : 0 ≤ restrictedGradientTest g Ω f f := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply integral_nonneg
  intro x
  change 0 ≤ inner ℝ (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient f x)
  exact real_inner_self_nonneg

private theorem restrictedGradientTest_self_le (g : RiemannianMetric 3 M) (Ω : Set M)
    (f : EnergyTest g.leviCivitaData univ) : restrictedGradientTest g Ω f f ≤ ‖f‖ ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  calc
    _ ≤ ∫ x, g.inner x (g.leviCivitaData.gradient f x)
        (g.leviCivitaData.gradient f x) ∂g.volumeMeasure := by
      apply setIntegral_le_integral (f.integrable_gradient f)
      exact Filter.Eventually.of_forall fun x => by
        change 0 ≤ inner ℝ (g.leviCivitaData.gradient f x) (g.leviCivitaData.gradient f x)
        exact real_inner_self_nonneg
    _ ≤ ‖f‖ ^ 2 := by
      rw [EnergyTest.norm_sq, energyInner]
      exact le_add_of_nonneg_left (integral_nonneg fun x => mul_self_nonneg (f x))

private def restrictedGradientTestCLM (g : RiemannianMetric 3 M) (Ω : Set M) :
    EnergyTest g.leviCivitaData univ →L[ℝ]
      EnergyTest g.leviCivitaData univ →L[ℝ] ℝ :=
  (restrictedGradientTestBilinear g Ω).mkContinuous₂ 1 (fun f h => by
    simpa only [one_mul] using bilinear_norm_le_of_nonnegative_quadratic_bound
      (restrictedGradientTestBilinear g Ω) (restrictedGradientTest_symm g Ω)
      (restrictedGradientTest_nonneg g Ω) (restrictedGradientTest_self_le g Ω) f h)

set_option synthInstance.maxHeartbeats 200000 in
/-- The continuous extension of the literal native domain gradient integral. -/
def nativeRestrictedGradientEnergy (g : RiemannianMetric 3 M) (Ω : Set M) :
    H1Zero g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  (((restrictedGradientTestCLM g Ω).extend
    (Completion.toComplL : EnergyTest g.leviCivitaData univ →L[ℝ]
      H1Zero g.leviCivitaData univ)).flip.extend
    (Completion.toComplL : EnergyTest g.leviCivitaData univ →L[ℝ]
      H1Zero g.leviCivitaData univ)).flip

@[simp] theorem nativeRestrictedGradientEnergy_coe (g : RiemannianMetric 3 M) (Ω : Set M)
    (f h : EnergyTest g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g Ω (f : H1Zero g.leviCivitaData univ)
      (h : H1Zero g.leviCivitaData univ) =
        ∫ x in Ω, g.inner x (g.leviCivitaData.gradient f x)
          (g.leviCivitaData.gradient h x) ∂g.volumeMeasure := by
  let ι : EnergyTest g.leviCivitaData univ →L[ℝ]
      H1Zero g.leviCivitaData univ := Completion.toComplL
  change ((((restrictedGradientTestCLM g Ω).extend ι).flip.extend ι) (ι h)) (ι f) = _
  rw [(((restrictedGradientTestCLM g Ω).extend ι).flip).extend_eq (e := ι)
    Completion.denseRange_coe (Completion.isUniformInducing_coe _) h,
    ContinuousLinearMap.flip_apply,
    (restrictedGradientTestCLM g Ω).extend_eq (e := ι)
      Completion.denseRange_coe (Completion.isUniformInducing_coe _) f]
  rfl

theorem nativeRestrictedGradientEnergy_symm (g : RiemannianMetric 3 M) (Ω : Set M)
    (v w : H1Zero g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g Ω v w = nativeRestrictedGradientEnergy g Ω w v := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f =>
    induction w using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih h =>
      rw [nativeRestrictedGradientEnergy_coe, nativeRestrictedGradientEnergy_coe]
      exact restrictedGradientTest_symm g Ω f h

theorem nativeRestrictedGradientEnergy_apply_norm_le (g : RiemannianMetric 3 M) (Ω : Set M)
    (v w : H1Zero g.leviCivitaData univ) :
    ‖nativeRestrictedGradientEnergy g Ω v w‖ ≤ ‖v‖ * ‖w‖ := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih f =>
    induction w using Completion.induction_on with
    | hp => apply isClosed_le <;> fun_prop
    | ih h =>
      simpa only [nativeRestrictedGradientEnergy_coe, Completion.norm_coe,
        restrictedGradientTestBilinear, LinearMap.mk₂_apply, restrictedGradientTest] using
        bilinear_norm_le_of_nonnegative_quadratic_bound
          (restrictedGradientTestBilinear g Ω) (restrictedGradientTest_symm g Ω)
          (restrictedGradientTest_nonneg g Ω) (restrictedGradientTest_self_le g Ω) f h

theorem nativeRestrictedGradientEnergy_norm_le (g : RiemannianMetric 3 M) (Ω : Set M) :
    ‖nativeRestrictedGradientEnergy g Ω‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one
  intro v w
  simpa only [one_mul] using nativeRestrictedGradientEnergy_apply_norm_le g Ω v w

/-- A domain H1-zero argument has zero exterior gradient contribution,
proved by genuine smooth support and completion density. -/
theorem nativeRestrictedGradientEnergy_domain_right (g : RiemannianMetric 3 M) (Ω : Set M)
    (v : H1Zero g.leviCivitaData univ) (z : H1Zero g.leviCivitaData Ω) :
    nativeRestrictedGradientEnergy g Ω v (nativeDomainEnergyInclusion g Ω z) =
      gradientEnergy g.leviCivitaData univ v (nativeDomainEnergyInclusion g Ω z) := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f =>
    induction z using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih h =>
      rw [nativeDomainEnergyInclusion_coe, nativeRestrictedGradientEnergy_coe, gradientEnergy_coe]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hxt : x ∉ tsupport (h : M → ℝ) := fun hh => hx (h.support_subset hh)
      have hgrad : g.leviCivitaData.gradient (nativeDomainTestInclusion g Ω h) x = 0 :=
        g.leviCivitaData.gradient_eq_zero_of_notMem_tsupport hxt
      rw [hgrad]
      simp

#print axioms nativeRestrictedGradientEnergy_coe
#print axioms nativeRestrictedGradientEnergy_norm_le
#print axioms nativeRestrictedGradientEnergy_domain_right

end Yamabe3.Analysis
