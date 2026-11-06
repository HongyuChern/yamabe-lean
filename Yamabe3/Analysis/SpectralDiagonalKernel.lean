import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Actual diagonal Green kernels on the Hilbert sequence space

The kernel is a continuous-linear operator on lp 2, not a coordinatewise
formal series. Its operator norm has a common exponential majorant even
for unbounded spectral rates. Continuity is proved by a uniform scalar
Lipschitz estimate, so no sum is interchanged with a time supremum.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped Topology lp
namespace Yamabe3.Analysis.Delaunay

abbrev SpectralSpace (ι : Type*) := lp (fun _ : ι => ℝ) 2

/-- A genuinely bounded diagonal operator on the actual Hilbert sequence space. -/
def spectralDiagonal {ι : Type*} (a : ι → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ B) : SpectralSpace ι →L[ℝ] SpectralSpace ι :=
  lp.mapCLM 2 (fun i => a i • ContinuousLinearMap.id ℝ ℝ) hB
    (fun i => by simpa only [norm_smul, ContinuousLinearMap.norm_id,
      Real.norm_eq_abs, mul_one] using ha i)

@[simp] theorem spectralDiagonal_apply {ι : Type*} (a : ι → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ B) (u : SpectralSpace ι) (i : ι) :
    spectralDiagonal a hB ha u i = a i * u i := rfl

theorem spectralDiagonal_norm_le {ι : Type*} (a : ι → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ B) : ‖spectralDiagonal a hB ha‖ ≤ B :=
  lp.norm_mapCLM_le 2 _ hB _

def scalarGreenKernel (k t : ℝ) : ℝ := -Real.exp (-k * |t|) / (2 * k)

theorem scalarGreenKernel_abs_le {k k₀ : ℝ} (hk₀ : 0 < k₀) (hk : k₀ ≤ k) (t : ℝ) :
    |scalarGreenKernel k t| ≤ Real.exp (-k₀ * |t|) / (2 * k₀) := by
  have hkpos : 0 < k := hk₀.trans_le hk
  unfold scalarGreenKernel
  rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity : 0 < 2 * k)]
  apply div_le_div₀ (Real.exp_pos _).le
  · exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg t])
  · positivity
  · linarith

/-- Uniform continuity survives arbitrarily high spectral rates. -/
theorem scalarGreenKernel_lipschitz {k : ℝ} (hk : 0 < k) (t s : ℝ) :
    |scalarGreenKernel k t - scalarGreenKernel k s| ≤ (1 / 2 : ℝ) * |t - s| := by
  let f : ℝ → ℝ := fun r => -Real.exp (-k * r) / (2 * k)
  have hd (r : ℝ) : HasDerivAt f (Real.exp (-k * r) / 2) r := by
    apply (((((hasDerivAt_id r).const_mul (-k)).exp).neg).div_const (2 * k)).congr_deriv
    dsimp
    field_simp
  have hb (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) : ‖Real.exp (-k * r) / 2‖ ≤ (1 / 2 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have he : Real.exp (-k * r) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) hr)
    linarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ Ici (0 : ℝ)) => (hd r).hasDerivWithinAt) hb
    (convex_Ici 0) (show |s| ∈ Ici (0 : ℝ) from abs_nonneg s)
    (show |t| ∈ Ici (0 : ℝ) from abs_nonneg t)
  change |scalarGreenKernel k t - scalarGreenKernel k s| ≤ (1 / 2 : ℝ) * |(|t| - |s|)| at h
  exact h.trans (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le t s) (by norm_num))

/-- The true diagonal full-line Green kernel for d²/dt²-k_i². -/
def spectralGreenKernel {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (t : ℝ) :
    SpectralSpace ι →L[ℝ] SpectralSpace ι :=
  spectralDiagonal (fun i => scalarGreenKernel (k i) t)
    (by positivity) (fun i => scalarGreenKernel_abs_le hk₀ (hk i) t)

@[simp] theorem spectralGreenKernel_apply {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (t : ℝ) (u : SpectralSpace ι) (i : ι) :
    spectralGreenKernel k hk₀ hk t u i = scalarGreenKernel (k i) t * u i := rfl

theorem spectralGreenKernel_norm_le {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (t : ℝ) :
    ‖spectralGreenKernel k hk₀ hk t‖ ≤ Real.exp (-k₀ * |t|) / (2 * k₀) :=
  spectralDiagonal_norm_le _ _ _

theorem spectralGreenKernel_lipschitz {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) :
    LipschitzWith (1 / 2) (spectralGreenKernel k hk₀ hk) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  let D := spectralDiagonal (fun i => scalarGreenKernel (k i) t - scalarGreenKernel (k i) s)
    (show 0 ≤ (1 / 2 : ℝ) * |t - s| by positivity)
    (fun i => scalarGreenKernel_lipschitz (hk₀.trans_le (hk i)) t s)
  have he : spectralGreenKernel k hk₀ hk t - spectralGreenKernel k hk₀ hk s = D := by
    ext u i
    change scalarGreenKernel (k i) t * u i - scalarGreenKernel (k i) s * u i =
      (scalarGreenKernel (k i) t - scalarGreenKernel (k i) s) * u i
    ring
  rw [dist_eq_norm, he]
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    spectralDiagonal_norm_le (fun i => scalarGreenKernel (k i) t - scalarGreenKernel (k i) s)
      (show 0 ≤ (1 / 2 : ℝ) * |t - s| by positivity)
      (fun i => scalarGreenKernel_lipschitz (hk₀.trans_le (hk i)) t s)

/-- Exponential conjugation of the actual operator kernel. -/
def weightedSpectralKernel {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ t : ℝ) :
    SpectralSpace ι →L[ℝ] SpectralSpace ι :=
  Real.exp (-δ * t) • spectralGreenKernel k hk₀ hk t

theorem weightedSpectralKernel_continuous {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ : ℝ) :
    Continuous (weightedSpectralKernel k hk₀ hk δ) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (spectralGreenKernel_lipschitz k hk₀ hk).continuous

theorem weightedSpectralKernel_norm_le {ι : Type*} (k : ι → ℝ) {k₀ : ℝ}
    (hk₀ : 0 < k₀) (hk : ∀ i, k₀ ≤ k i) (δ t : ℝ) :
    ‖weightedSpectralKernel k hk₀ hk δ t‖ ≤
      Real.exp (-δ * t - k₀ * |t|) / (2 * k₀) := by
  rw [weightedSpectralKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-δ * t) * (Real.exp (-k₀ * |t|) / (2 * k₀)) :=
      mul_le_mul_of_nonneg_left (spectralGreenKernel_norm_le k hk₀ hk t) (Real.exp_pos _).le
    _ = _ := by rw [← mul_div_assoc, ← Real.exp_add]; congr 2; ring

end Yamabe3.Analysis.Delaunay
