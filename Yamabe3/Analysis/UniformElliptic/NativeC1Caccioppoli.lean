import Yamabe3.Analysis.UniformElliptic.NativeC1StrongLimit
import PoincareLib.Analysis.Elliptic.Regularity.WeakTestExtension

/-!
# Fixed-cutoff Caccioppoli and two-index gradient convergence at C1 regularity

The weak equation is tested with the actual compact H1 function eta^2 u
using the pinned Sobolev test-extension theorem. No C1 function is promoted
to smoothness. If every coordinate partial of eta has absolute value at
most B, the explicit constant is 1 + 4 d B^2. It is fixed before u and f.

The final consumer retains the literal source f/8 + Q*u for one and the
same bounded potential Q. Two-index L2 differences of the actual values
and the actual physical sources then force the actual gradients to be
Cauchy on the smaller region. No common energy bound is substituted for
this difference estimate, and no boundary trace condition is imposed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem c1_memLp_bounded_mul
    {μ : Measure E} {a u : E → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)
    (hu : MemLp u 2 μ) : MemLp (fun x => a x * u x) 2 μ := by
  apply hu.of_le_mul (c := C) (ha.mul hu.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- The cutoff test is a genuine compact H1 test. The gradient bound is
weighted by the literal cutoff and its constant is entirely explicit. -/
theorem native_H1_cutoff_gradient_integral_le
    {Ω : Set E} (hΩ : IsOpen Ω) {η : E → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hDη : ∀ x (i : Fin d), |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B)
    {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω))
    (hf : MemLp f 2 (volume.restrict Ω))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict Ω))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u Ω)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, p i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, f x * φ x) :
    (∫ x in Ω, ∑ i : Fin d, (η x * p i x) ^ 2) ≤
      (1 + 4 * (d : ℝ) * B ^ 2) * ((∫ x in Ω, u x ^ 2) + ∫ x in Ω, f x ^ 2) := by
  classical
  let μ := volume.restrict Ω
  let Dη : Fin d → E → ℝ := fun i x => fderiv ℝ η x (EuclideanSpace.single i 1)
  let φ : E → ℝ := fun x => (η x * η x) * u x
  let q : Fin d → E → ℝ := fun i x =>
    η x * (η x * p i x) + 2 * (η x * (Dη i x * u x))
  have hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg ((hηrange x).1)]
    exact (hηrange x).2
  have hηmul {v : E → ℝ} (hv : MemLp v 2 μ) :
      MemLp (fun x => η x * v x) 2 μ :=
    c1_memLp_bounded_mul hη.continuous.aestronglyMeasurable hηbound hv
  have hDu (i : Fin d) : MemLp (fun x => Dη i x * u x) 2 μ :=
    c1_memLp_bounded_mul
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hDη x i) hu
  have hφLp : MemLp φ 2 μ := by
    simpa only [φ, mul_assoc] using hηmul (hηmul hu)
  have hqLp (i : Fin d) : MemLp (q i) 2 μ :=
    (hηmul (hηmul (hp i))).add ((hηmul (hDu i)).const_mul 2)
  have hDsq (x : E) (i : Fin d) :
      fderiv ℝ (fun y => η y * η y) x (EuclideanSpace.single i 1) =
        2 * η x * Dη i x := by
    rw [fderiv_fun_mul (hη.differentiable (by simp) x) (hη.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, Dη]
    ring
  have hqWeak (i : Fin d) : HasWeakPartialDeriv i (q i) φ Ω := by
    have h := (hw i).mul_smooth hΩ (hη.mul hη)
      (hu.locallyIntegrable (by norm_num)) ((hp i).locallyIntegrable (by norm_num))
    have hqeq : q i = fun x => (η x * η x) * p i x +
        fderiv ℝ (fun y => η y * η y) x (EuclideanSpace.single i 1) * u x := by
      funext x
      rw [hDsq]
      dsimp only [q]
      ring
    rw [hqeq]
    exact h
  have hφc : HasCompactSupport φ := hηc.mul_right.mul_right
  have hφΩ : tsupport φ ⊆ Ω :=
    (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hηΩ
  have htest := weakEquation_of_compact_memW1p hΩ hp hf heq hφLp hqLp hqWeak hφc hφΩ
  have hA : Integrable (fun x => ∑ i : Fin d, (η x * p i x) ^ 2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hηmul (hp i)).integrable_sq)
  have hK : Integrable (fun x => ∑ i : Fin d, p i x * q i x) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hp i).integrable_mul (hqLp i))
  have hD : Integrable (fun x => ∑ i : Fin d, (Dη i x * u x) ^ 2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hDu i).integrable_sq)
  have hpoint (x : E) : (∑ i : Fin d, (η x * p i x) ^ 2) ≤
      2 * (∑ i : Fin d, p i x * q i x) + 4 * (∑ i : Fin d, (Dη i x * u x) ^ 2) := by
    have h (i : Fin d) : (η x * p i x) ^ 2 ≤
        2 * (p i x * q i x) + 4 * (Dη i x * u x) ^ 2 := by
      dsimp only [q]
      nlinarith [sq_nonneg (η x * p i x + 2 * Dη i x * u x)]
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  have henergy : (∫ x in Ω, ∑ i : Fin d, (η x * p i x) ^ 2) ≤
      ∫ x in Ω, 2 * (∑ i : Fin d, p i x * q i x) +
        4 * (∑ i : Fin d, (Dη i x * u x) ^ 2) :=
    integral_mono hA ((hK.const_mul 2).add (hD.const_mul 4)) hpoint
  rw [integral_add (hK.const_mul 2) (hD.const_mul 4), integral_const_mul,
    integral_const_mul, htest] at henergy
  have hsource : 2 * (∫ x in Ω, f x * φ x) ≤
      (∫ x in Ω, u x ^ 2) + ∫ x in Ω, f x ^ 2 := by
    calc
      _ = ∫ x in Ω, 2 * (f x * φ x) := (integral_const_mul _ _).symm
      _ ≤ ∫ x in Ω, u x ^ 2 + f x ^ 2 := by
        apply integral_mono ((hf.integrable_mul hφLp).const_mul 2)
          (hu.integrable_sq.add hf.integrable_sq)
        intro x
        change 2 * (f x * φ x) ≤ u x ^ 2 + f x ^ 2
        have hηsq : 0 ≤ η x * η x ∧ η x * η x ≤ 1 := by
          constructor
          · exact mul_nonneg (hηrange x).1 (hηrange x).1
          · nlinarith [(hηrange x).1, (hηrange x).2]
        have hφnorm : ‖φ x‖ ≤ ‖u x‖ := by
          dsimp only [φ]
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hηsq.1]
          exact mul_le_of_le_one_left (norm_nonneg _) hηsq.2
        have hφsq : φ x ^ 2 ≤ u x ^ 2 := by
          simpa only [Real.norm_eq_abs, sq_abs] using
            pow_le_pow_left₀ (norm_nonneg (φ x)) hφnorm 2
        nlinarith [sq_nonneg (f x - φ x)]
      _ = _ := integral_add hu.integrable_sq hf.integrable_sq
  have hcut : (∫ x in Ω, ∑ i : Fin d, (Dη i x * u x) ^ 2) ≤
      (d : ℝ) * B ^ 2 * (∫ x in Ω, u x ^ 2) := by
    calc
      _ ≤ ∫ x in Ω, ((d : ℝ) * B ^ 2) * u x ^ 2 := by
        apply integral_mono hD (hu.integrable_sq.const_mul _)
        intro x
        change (∑ i : Fin d, (Dη i x * u x) ^ 2) ≤
          ((d : ℝ) * B ^ 2) * u x ^ 2
        have hi (i : Fin d) : (Dη i x * u x) ^ 2 ≤ B ^ 2 * u x ^ 2 := by
          have hsq : Dη i x ^ 2 ≤ B ^ 2 := by
            simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Dη i x)) (hDη x i) 2
          simpa only [mul_pow] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (u x))
        calc
          _ ≤ ∑ _i : Fin d, B ^ 2 * u x ^ 2 :=
            Finset.sum_le_sum fun i _ => hi i
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]; ring
      _ = _ := integral_const_mul _ _
  have hfnon : 0 ≤ ∫ x in Ω, f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  calc
    _ ≤ 2 * (∫ x in Ω, f x * φ x) +
        4 * (∫ x in Ω, ∑ i : Fin d, (Dη i x * u x) ^ 2) := henergy
    _ ≤ ((∫ x in Ω, u x ^ 2) + ∫ x in Ω, f x ^ 2) +
        4 * ((d : ℝ) * B ^ 2 * (∫ x in Ω, u x ^ 2)) :=
      add_le_add hsource (mul_le_mul_of_nonneg_left hcut (by norm_num))
    _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * (d : ℝ) * B ^ 2) hfnon]

/-- Restrict the genuine weighted estimate to a measurable region on
which the fixed cutoff is identically one. -/
theorem native_H1_gradient_integral_le
    {Ω W : Set E} (hΩ : IsOpen Ω) (hW : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηone : ∀ x ∈ W, η x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hDη : ∀ x (i : Fin d), |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B)
    {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict Ω))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u Ω)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, p i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, f x * φ x) :
    (∫ x in W, ∑ i : Fin d, p i x ^ 2) ≤
      (1 + 4 * (d : ℝ) * B ^ 2) * ((∫ x in Ω, u x ^ 2) + ∫ x in Ω, f x ^ 2) := by
  have hηbound : ∀ᵐ x ∂(volume.restrict Ω), ‖η x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg ((hηrange x).1)]
    exact (hηrange x).2
  have hi : Integrable (fun x => ∑ i : Fin d, (η x * p i x) ^ 2)
      (volume.restrict Ω) := integrable_finsetSum Finset.univ fun i _ =>
    (c1_memLp_bounded_mul hη.continuous.aestronglyMeasurable hηbound (hp i)).integrable_sq
  calc
    _ = ∫ x in W, ∑ i : Fin d, (η x * p i x) ^ 2 := by
      apply setIntegral_congr_fun hW
      intro x hx
      simp only [hηone x hx, one_mul]
    _ ≤ ∫ x in Ω, ∑ i : Fin d, (η x * p i x) ^ 2 :=
      setIntegral_mono_set hi (Eventually.of_forall fun x =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _) (Eventually.of_forall fun x => @hWΩ x)
    _ ≤ _ := native_H1_cutoff_gradient_integral_le (u := u) (f := f) (p := p)
      hΩ hη hηc hηΩ hηrange hB hDη
      hu hf hp hw heq

/-- The gradient in the estimate is the actual classical gradient of
the same locally C1 field; its weak derivative identity is proved. -/
theorem native_C1_gradient_integral_le
    {Ω W : Set E} (hΩ : IsOpen Ω) (hW : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηone : ∀ x ∈ W, η x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hDη : ∀ x (i : Fin d), |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B)
    {u f : E → ℝ} (hC1 : ContDiffOn ℝ 1 u Ω)
    (hu : MemLp u 2 (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (hp : ∀ i, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      2 (volume.restrict Ω))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, fderiv ℝ u x (EuclideanSpace.single i 1) *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in Ω, f x * φ x) :
    (∫ x in W, ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
      (1 + 4 * (d : ℝ) * B ^ 2) * ((∫ x in Ω, u x ^ 2) + ∫ x in Ω, f x ^ 2) :=
  native_H1_gradient_integral_le (u := u) (f := f)
    (p := fun i x => fderiv ℝ u x (EuclideanSpace.single i 1))
    hΩ hW hWΩ hη hηc hηΩ hηrange hηone hB hDη
    hu hf hp (fun i => native_hasWeakPartialDeriv_of_contDiffOn_one hΩ hC1 i) heq

private theorem c1_weak_partial_sub {Ω : Set E} {u v p q : E → ℝ} (i : Fin d)
    (hu : MemLp u 2 (volume.restrict Ω)) (hv : MemLp v 2 (volume.restrict Ω))
    (hp : MemLp p 2 (volume.restrict Ω)) (hq : MemLp q 2 (volume.restrict Ω))
    (hup : HasWeakPartialDeriv i p u Ω) (hvq : HasWeakPartialDeriv i q v Ω) :
    HasWeakPartialDeriv i (fun x => p x - q x) (fun x => u x - v x) Ω := by
  intro φ hφ hc hs
  have hφL : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hDφL : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
      2 (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict Ω
  change (∫ x in Ω, (u x - v x) * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
    -(∫ x in Ω, (p x - q x) * φ x)
  have huI : Integrable (fun x => u x * fderiv ℝ φ x (EuclideanSpace.single i 1))
      (volume.restrict Ω) := hu.integrable_mul hDφL
  have hvI : Integrable (fun x => v x * fderiv ℝ φ x (EuclideanSpace.single i 1))
      (volume.restrict Ω) := hv.integrable_mul hDφL
  have hpI : Integrable (fun x => p x * φ x) (volume.restrict Ω) :=
    hp.integrable_mul hφL
  have hqI : Integrable (fun x => q x * φ x) (volume.restrict Ω) :=
    hq.integrable_mul hφL
  simp_rw [sub_mul]
  rw [integral_sub huI hvI, integral_sub hpI hqI,
    hup φ hφ hc hs, hvq φ hφ hc hs]
  ring

private theorem c1_weakEquation_sub {Ω : Set E} {p q : Fin d → E → ℝ} {f g : E → ℝ}
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict Ω))
    (hq : ∀ i, MemLp (q i) 2 (volume.restrict Ω))
    (hf : MemLp f 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hep : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, p i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, f x * φ x)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, q i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, g x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, (p i x - q i x) * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, (f x - g x) * φ x := by
  intro φ hφ hc hs
  have hφL : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hd (i : Fin d) : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
      2 (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict Ω
  have hip : Integrable (fun x => ∑ i : Fin d, p i x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) (volume.restrict Ω) :=
    integrable_finsetSum Finset.univ fun i _ => (hp i).integrable_mul (hd i)
  have hiq : Integrable (fun x => ∑ i : Fin d, q i x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) (volume.restrict Ω) :=
    integrable_finsetSum Finset.univ fun i _ => (hq i).integrable_mul (hd i)
  have hfI : Integrable (fun x => f x * φ x) (volume.restrict Ω) :=
    hf.integrable_mul hφL
  have hgI : Integrable (fun x => g x * φ x) (volume.restrict Ω) :=
    hg.integrable_mul hφL
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [integral_sub hip hiq, integral_sub hfI hgI,
    hep φ hφ hc hs, heq φ hφ hc hs]

/-- Two-index smallness of the actual values and principal sources
implies two-index smallness of the genuine weak gradients on the smaller
region. The single cutoff constant precedes both indices. -/
theorem native_H1_gradient_cauchy_of_value_source_cauchy
    {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {Ω W : Set E} (hΩ : IsOpen Ω) (hW : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηone : ∀ x ∈ W, η x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hDη : ∀ x (i : Fin d), |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B)
    {u f : ι → E → ℝ} {p : ι → Fin d → E → ℝ}
    (hu : ∀ a, MemLp (u a) 2 (volume.restrict Ω))
    (hf : ∀ a, MemLp (f a) 2 (volume.restrict Ω))
    (hp : ∀ a i, MemLp (p a i) 2 (volume.restrict Ω))
    (hw : ∀ a i, HasWeakPartialDeriv i (p a i) (u a) Ω)
    (heq : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, p a i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, f a x * φ x)
    (huc : Tendsto (fun ab : ι × ι => ∫ x in Ω, (u ab.1 x - u ab.2 x) ^ 2) atTop (𝓝 0))
    (hfc : Tendsto (fun ab : ι × ι => ∫ x in Ω, (f ab.1 x - f ab.2 x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun ab : ι × ι => ∫ x in W, ∑ i : Fin d,
      (p ab.1 i x - p ab.2 i x) ^ 2) atTop (𝓝 0) := by
  have hbound (ab : ι × ι) := native_H1_gradient_integral_le
    (u := fun x => u ab.1 x - u ab.2 x)
    (f := fun x => f ab.1 x - f ab.2 x)
    (p := fun i x => p ab.1 i x - p ab.2 i x)
    hΩ hW hWΩ hη hηc hηΩ hηrange hηone hB hDη
    ((hu ab.1).sub (hu ab.2)) ((hf ab.1).sub (hf ab.2))
    (fun i => (hp ab.1 i).sub (hp ab.2 i))
    (fun i => c1_weak_partial_sub i (hu ab.1) (hu ab.2) (hp ab.1 i) (hp ab.2 i)
      (hw ab.1 i) (hw ab.2 i))
    (c1_weakEquation_sub (hp ab.1) (hp ab.2) (hf ab.1) (hf ab.2) (heq ab.1) (heq ab.2))
  apply squeeze_zero (fun _ => integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    hbound
  simpa using (huc.add hfc).const_mul (1 + 4 * (d : ℝ) * B ^ 2)

/-- The C1 specialization identifies every gradient with the actual
classical first derivatives of the original, unmodified fields. -/
theorem native_C1_gradient_cauchy_of_value_source_cauchy
    {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {Ω W : Set E} (hΩ : IsOpen Ω) (hW : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηone : ∀ x ∈ W, η x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hDη : ∀ x (i : Fin d), |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B)
    {u f : ι → E → ℝ} (hC1 : ∀ a, ContDiffOn ℝ 1 (u a) Ω)
    (hu : ∀ a, MemLp (u a) 2 (volume.restrict Ω))
    (hf : ∀ a, MemLp (f a) 2 (volume.restrict Ω))
    (hp : ∀ a i, MemLp (fun x => fderiv ℝ (u a) x (EuclideanSpace.single i 1))
      2 (volume.restrict Ω))
    (heq : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, fderiv ℝ (u a) x (EuclideanSpace.single i 1) *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in Ω, f a x * φ x)
    (huc : Tendsto (fun ab : ι × ι => ∫ x in Ω, (u ab.1 x - u ab.2 x) ^ 2) atTop (𝓝 0))
    (hfc : Tendsto (fun ab : ι × ι => ∫ x in Ω, (f ab.1 x - f ab.2 x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun ab : ι × ι => ∫ x in W, ∑ i : Fin d,
      (fderiv ℝ (u ab.1) x (EuclideanSpace.single i 1) -
        fderiv ℝ (u ab.2) x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0) :=
  native_H1_gradient_cauchy_of_value_source_cauchy (u := u) (f := f)
    (p := fun a i x => fderiv ℝ (u a) x (EuclideanSpace.single i 1))
    hΩ hW hWΩ hη hηc hηΩ hηrange
    hηone hB hDη hu hf hp
    (fun a i => native_hasWeakPartialDeriv_of_contDiffOn_one hΩ (hC1 a) i) heq huc hfc

/-- The literal physical source divided by eight and one fixed bounded
potential preserve two-index L2 Cauchy convergence. The numerical source
coefficient in the square estimate is 1/32. -/
theorem native_fixed_potential_source_cauchy
    {ι : Type*} [Nonempty ι] [SemilatticeSup ι] {Ω : Set E}
    {u f : ι → E → ℝ} {Q : E → ℝ} {C : ℝ}
    (hQ : AEStronglyMeasurable Q (volume.restrict Ω))
    (hQbound : ∀ᵐ x ∂(volume.restrict Ω), ‖Q x‖ ≤ C)
    (hu : ∀ a, MemLp (u a) 2 (volume.restrict Ω))
    (hf : ∀ a, MemLp (f a) 2 (volume.restrict Ω))
    (huc : Tendsto (fun ab : ι × ι => ∫ x in Ω, (u ab.1 x - u ab.2 x) ^ 2) atTop (𝓝 0))
    (hfc : Tendsto (fun ab : ι × ι => ∫ x in Ω, (f ab.1 x - f ab.2 x) ^ 2) atTop (𝓝 0)) :
    (∀ a, MemLp (fun x => f a x / 8 + Q x * u a x) 2 (volume.restrict Ω)) ∧
      Tendsto (fun ab : ι × ι => ∫ x in Ω,
        ((f ab.1 x / 8 + Q x * u ab.1 x) - (f ab.2 x / 8 + Q x * u ab.2 x)) ^ 2)
        atTop (𝓝 0) := by
  have hg (a : ι) : MemLp (fun x => f a x / 8 + Q x * u a x)
      2 (volume.restrict Ω) := by
    have hscale : MemLp (fun x => f a x / 8) 2 (volume.restrict Ω) := by
      simpa only [div_eq_mul_inv] using (hf a).mul_const (8 : ℝ)⁻¹
    have hpot : MemLp (fun x => Q x * u a x) 2 (volume.restrict Ω) :=
      c1_memLp_bounded_mul hQ hQbound (hu a)
    exact hscale.add hpot
  refine ⟨hg, ?_⟩
  have hupper (ab : ι × ι) :
      (∫ x in Ω, ((f ab.1 x / 8 + Q x * u ab.1 x) -
        (f ab.2 x / 8 + Q x * u ab.2 x)) ^ 2) ≤
      (1 / 32 : ℝ) * (∫ x in Ω, (f ab.1 x - f ab.2 x) ^ 2) +
        (2 * C ^ 2) * (∫ x in Ω, (u ab.1 x - u ab.2 x) ^ 2) := by
    have hfi : Integrable (fun x => (f ab.1 x - f ab.2 x) ^ 2)
        (volume.restrict Ω) := ((hf ab.1).sub (hf ab.2)).integrable_sq
    have hui : Integrable (fun x => (u ab.1 x - u ab.2 x) ^ 2)
        (volume.restrict Ω) := ((hu ab.1).sub (hu ab.2)).integrable_sq
    calc
      _ ≤ ∫ x in Ω, (1 / 32 : ℝ) * (f ab.1 x - f ab.2 x) ^ 2 +
          (2 * C ^ 2) * (u ab.1 x - u ab.2 x) ^ 2 := by
        apply integral_mono_ae ((hg ab.1).sub (hg ab.2)).integrable_sq
          ((hfi.const_mul _).add (hui.const_mul _))
        filter_upwards [hQbound] with x hx
        simp only [Pi.sub_apply, Pi.add_apply]
        have hqsq : Q x ^ 2 ≤ C ^ 2 := by
          simpa only [Real.norm_eq_abs, sq_abs] using
            pow_le_pow_left₀ (norm_nonneg (Q x)) hx 2
        have hprod := mul_le_mul_of_nonneg_right hqsq
          (sq_nonneg (u ab.1 x - u ab.2 x))
        have hd : (f ab.1 x / 8 + Q x * u ab.1 x) -
            (f ab.2 x / 8 + Q x * u ab.2 x) =
            (f ab.1 x - f ab.2 x) / 8 + Q x * (u ab.1 x - u ab.2 x) := by ring
        rw [hd]
        nlinarith [sq_nonneg ((f ab.1 x - f ab.2 x) / 8 - Q x * (u ab.1 x - u ab.2 x))]
      _ = _ := by
        rw [integral_add (hfi.const_mul _) (hui.const_mul _),
          integral_const_mul, integral_const_mul]
  apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) hupper
  simpa using (hfc.const_mul (1 / 32 : ℝ)).add (huc.const_mul (2 * C ^ 2))

/-- A same-potential physical equation with the actual source divided by
eight produces strong two-index gradient smallness on a fixed smaller
region. No regularity of the source beyond L2 is required. -/
theorem native_C1_gradient_cauchy_of_fixed_potential
    {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {Ω W : Set E} (hΩ : IsOpen Ω) (hW : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηone : ∀ x ∈ W, η x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hDη : ∀ x (i : Fin d), |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B)
    {u f : ι → E → ℝ} {Q : E → ℝ} {C : ℝ}
    (hQ : AEStronglyMeasurable Q (volume.restrict Ω))
    (hQbound : ∀ᵐ x ∂(volume.restrict Ω), ‖Q x‖ ≤ C)
    (hC1 : ∀ a, ContDiffOn ℝ 1 (u a) Ω)
    (hu : ∀ a, MemLp (u a) 2 (volume.restrict Ω))
    (hf : ∀ a, MemLp (f a) 2 (volume.restrict Ω))
    (hp : ∀ a i, MemLp (fun x => fderiv ℝ (u a) x (EuclideanSpace.single i 1))
      2 (volume.restrict Ω))
    (heq : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, fderiv ℝ (u a) x (EuclideanSpace.single i 1) *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, (f a x / 8 + Q x * u a x) * φ x)
    (huc : Tendsto (fun ab : ι × ι => ∫ x in Ω, (u ab.1 x - u ab.2 x) ^ 2) atTop (𝓝 0))
    (hfc : Tendsto (fun ab : ι × ι => ∫ x in Ω, (f ab.1 x - f ab.2 x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun ab : ι × ι => ∫ x in W, ∑ i : Fin d,
      (fderiv ℝ (u ab.1) x (EuclideanSpace.single i 1) -
        fderiv ℝ (u ab.2) x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0) := by
  obtain ⟨hg, hgc⟩ := native_fixed_potential_source_cauchy (u := u) (f := f)
    (Q := Q) (C := C) hQ hQbound hu hf huc hfc
  exact native_C1_gradient_cauchy_of_value_source_cauchy (u := u)
    (f := fun a x => f a x / 8 + Q x * u a x) hΩ hW hWΩ hη hηc hηΩ hηrange
    hηone hB hDη hC1 hu hg hp heq huc hgc

#print axioms native_H1_cutoff_gradient_integral_le
#print axioms native_H1_gradient_integral_le
#print axioms native_C1_gradient_integral_le
#print axioms native_H1_gradient_cauchy_of_value_source_cauchy
#print axioms native_C1_gradient_cauchy_of_value_source_cauchy
#print axioms native_fixed_potential_source_cauchy
#print axioms native_C1_gradient_cauchy_of_fixed_potential

end Yamabe3.Analysis.UniformElliptic
