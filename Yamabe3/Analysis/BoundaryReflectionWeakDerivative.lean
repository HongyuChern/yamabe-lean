import Yamabe3.Analysis.BoundaryFiniteReflection

/-! Moment cancellation gives a genuine distributional derivative across
the face. No pointwise trace of a weak function is postulated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.BoundaryTangential Poincare.Analysis.Sobolev.Weak
variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)

def reflectionDerivativeCoeffs (r c : ι → ℝ) (i : Fin d) (j : ι) : ℝ :=
  c j * normalFactor (-r j) i

def reflectionDual (r : ι → ℝ) (hr : ∀ j, 0 < r j) (c : ι → ℝ)
    (φ : E → ℝ) (x : E) : ℝ :=
  φ x + ∑ j, c j * (r j)⁻¹ * φ ((scaledReflect (r j) (hr j)).symm x)

theorem contDiff_reflectionDual (r : ι → ℝ) (hr : ∀ j, 0 < r j) (c : ι → ℝ)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (reflectionDual r hr c φ) :=
  hφ.add (ContDiff.sum (fun j _ => contDiff_const.mul
    (hφ.comp (scaledReflect (r j) (hr j)).symm.contDiff)))

theorem hasCompactSupport_reflectionDual (r : ι → ℝ) (hr : ∀ j, 0 < r j) (c : ι → ℝ)
    {φ : E → ℝ} (hc : HasCompactSupport φ) : HasCompactSupport (reflectionDual r hr c φ) := by
  classical
  apply hc.add
  have hh (s : Finset ι) : HasCompactSupport (fun x => ∑ j ∈ s,
      c j * (r j)⁻¹ * φ ((scaledReflect (r j) (hr j)).symm x)) := by
    induction s using Finset.induction_on with
    | empty => simp [HasCompactSupport]
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((hc.comp_homeomorph (scaledReflect (r a) (hr a)).symm.toHomeomorph).mul_left).add ih
  exact hh Finset.univ

theorem reflectionDual_derivative (r : ι → ℝ) (hr : ∀ j, 0 < r j) (c : ι → ℝ)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin d) (x : E) :
    fderiv ℝ (reflectionDual r hr (reflectionDerivativeCoeffs r c i) φ) x (EuclideanSpace.single i 1) =
      reflectionDual r hr c (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x := by
  let a (j : ι) := reflectionDerivativeCoeffs r c i j * (r j)⁻¹
  have hj (j : ι) := ((hφ.differentiable (by simp) _).hasFDerivAt.comp x
    (scaledReflect (r j) (hr j)).symm.toContinuousLinearMap.hasFDerivAt).const_mul (a j)
  have hd := ((hφ.differentiable (by simp) x).hasFDerivAt.add
    (HasFDerivAt.sum (fun j (_ : j ∈ Finset.univ) => hj j))).fderiv
  have heq : (φ + ∑ j, fun y => a j * (φ ∘ (scaledReflect (r j) (hr j)).symm.toContinuousLinearMap) y) =
      reflectionDual r hr (reflectionDerivativeCoeffs r c i) φ := by
    funext y
    simp only [Pi.add_apply, Finset.sum_apply, Function.comp_def, reflectionDual, a]
    rfl
  rw [heq] at hd
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, reflectionDual]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hder := reflected_test_partial_scaled (r j) (hr j) hφ i x
  have hdj := ((hφ.differentiable (by simp) _).hasFDerivAt.comp x
    (scaledReflect (r j) (hr j)).symm.toContinuousLinearMap.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => φ ((scaledReflect (r j) (hr j)).symm y)) x = _ at hdj
  rw [hdj] at hder
  change (fderiv ℝ φ ((scaledReflect (r j) (hr j)).symm x))
    ((scaledReflect (r j) (hr j)).symm (EuclideanSpace.single i 1)) = _ at hder
  change a j * (fderiv ℝ φ ((scaledReflect (r j) (hr j)).symm x))
    ((scaledReflect (r j) (hr j)).symm (EuclideanSpace.single i 1)) = _
  rw [hder]
  dsimp only [a, reflectionDerivativeCoeffs]
  by_cases hi : i = 0
  · subst i
    simp [normalFactor, inv_neg]
    field_simp [(hr j).ne']
  · simp only [normalFactor, if_neg hi, mul_one, one_mul]

theorem reflectionDual_normal_face (r : ι → ℝ) (hr : ∀ j, 0 < r j) (c : ι → ℝ)
    (hcs : ∑ j, c j = 1) (φ : E → ℝ) {x : E} (hx : x 0 = 0) :
    reflectionDual r hr (reflectionDerivativeCoeffs r c (0 : Fin d)) φ x = 0 := by
  have hf (j : ι) : (scaledReflect (r j) (hr j)).symm x = x := by
    ext i
    change normalFactor (-r j)⁻¹ i * x i = x i
    by_cases hi : i = 0
    · subst i; simp [hx]
    · simp [normalFactor, hi]
  have hcj (j : ι) : reflectionDerivativeCoeffs r c (0 : Fin d) j * (r j)⁻¹ = -c j := by
    simp [reflectionDerivativeCoeffs, normalFactor, (hr j).ne', ← mul_assoc]
  simp only [reflectionDual, hf, hcj]
  rw [← Finset.sum_mul, Finset.sum_neg_distrib, hcs]
  ring

theorem hasWeakPartialDeriv_finiteReflection
    (r : ι → ℝ) (hr : ∀ j, 0 < r j) (c : ι → ℝ) (hcs : ∑ j, c j = 1)
    {u g : E → ℝ} (i : Fin d)
    (hu : MemLp u 2 (volume.restrict (halfSpace d)))
    (hg : MemLp g 2 (volume.restrict (halfSpace d)))
    (hw : HasWeakPartialDeriv i g u (halfSpace d)) :
    HasWeakPartialDeriv i (finiteReflection r hr (reflectionDerivativeCoeffs r c i) g)
      (finiteReflection r hr c u) univ := by
  intro φ hφ hc _
  let ψ := reflectionDual r hr (reflectionDerivativeCoeffs r c i) φ
  have hs := contDiff_reflectionDual r hr (reflectionDerivativeCoeffs r c i) hφ
  have hsc := hasCompactSupport_reflectionDual r hr (reflectionDerivativeCoeffs r c i) hc
  have hface : i = 0 → ∀ x : E, x 0 = 0 → ψ x = 0 := by
    intro hi x hx; subst i
    exact reflectionDual_normal_face r hr c hcs φ hx
  have ht := weakPartial_test_upToBoundary (by norm_num : (1:ℝ≥0∞) ≤ 2) i hu hg hw hs hsc hface
  simp only [Measure.restrict_univ]
  rw [integral_finiteReflection r hr c hu
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)),
    integral_finiteReflection r hr (reflectionDerivativeCoeffs r c i) hg hφ.continuous hc]
  refine Eq.trans ?_ ht
  apply integral_congr_ae
  exact Eventually.of_forall fun x => congrArg (u x * ·)
    (reflectionDual_derivative r hr c hφ i x).symm

#print axioms hasWeakPartialDeriv_finiteReflection
end Yamabe3.Analysis.UniformElliptic
