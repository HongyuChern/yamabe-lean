import Yamabe3.Analysis.DelaunayEnergy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Genuine low-mode Jacobi fields of the constructed Delaunay orbit

The phase derivative and both first spherical modes are actual derivatives
of the previously constructed smooth orbit. The first modes have strict
positivity and an explicitly nonzero Wronskian at negative energy. These are
inputs to the low-mode inverse, not an assertion of a weighted inverse.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

/-- The normalized three-dimensional radial nonlinearity. -/
def radialForce (x : ℝ) : ℝ := x / 4 - 3 * x ^ 5 / 4

/-- Actual one-dimensional Jacobi operator for spherical eigenvalue λ. -/
def modelJacobi (v : ℝ → ℝ) (eigenvalue : ℝ) (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv ψ) t - (1 / 4 + eigenvalue) * ψ t + 15 / 4 * v t ^ 4 * ψ t

/-- The two strictly positive flux factors. -/
def modeFlux (v : ℝ → ℝ) (σ t : ℝ) : ℝ := v t / 2 + σ * deriv v t

/-- The actual first spherical Jacobi mode for σ=±1. -/
def translationMode (v : ℝ → ℝ) (σ t : ℝ) : ℝ := Real.exp (σ * t) * modeFlux v σ t

theorem radialForce_hasDerivAt (x : ℝ) :
    HasDerivAt radialForce ((1 - 15 * x ^ 4) / 4) x := by
  unfold radialForce
  apply (((hasDerivAt_id x).div_const 4).sub
    ((((hasDerivAt_id x).pow 5).const_mul 3).div_const 4)).congr_deriv
  norm_num
  ring

private theorem smooth_deriv {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (deriv v) := (contDiff_infty_iff_deriv.mp hv).2

theorem phase_mode_jacobi {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hode : ∀ t, deriv (deriv v) t = radialForce (v t)) (t : ℝ) :
    modelJacobi v 0 (deriv v) t = 0 := by
  have hid : deriv (deriv v) = fun s => radialForce (v s) := funext hode
  have hD := ((radialForce_hasDerivAt (v t)).comp t
    (hv.differentiable (by simp) t).hasDerivAt).deriv
  simp only [Function.comp_def] at hD
  unfold modelJacobi
  rw [hid, hD]
  ring

theorem modeFlux_contDiff {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (σ : ℝ) :
    ContDiff ℝ ∞ (modeFlux v σ) :=
  (hv.div_const 2).add (contDiff_const.mul (smooth_deriv hv))

theorem modeFlux_hasDerivAt {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hode : ∀ t, deriv (deriv v) t = radialForce (v t)) (σ t : ℝ) :
    HasDerivAt (modeFlux v σ) (deriv v t / 2 + σ * radialForce (v t)) t := by
  have hD := (hv.differentiable (by simp) t).hasDerivAt
  have hDD := ((smooth_deriv hv).differentiable (by simp) t).hasDerivAt.congr_deriv (hode t)
  exact (hD.div_const 2).add (hDD.const_mul σ)

theorem modeFlux_second {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hode : ∀ t, deriv (deriv v) t = radialForce (v t)) (σ t : ℝ) :
    deriv (deriv (modeFlux v σ)) t = radialForce (v t) / 2 +
      σ * ((1 - 15 * v t ^ 4) / 4 * deriv v t) := by
  have hdf : deriv (modeFlux v σ) = fun s => deriv v s / 2 + σ * radialForce (v s) :=
    funext fun s => (modeFlux_hasDerivAt hv hode σ s).deriv
  rw [hdf]
  have hD := (hv.differentiable (by simp) t).hasDerivAt
  have hDD := ((smooth_deriv hv).differentiable (by simp) t).hasDerivAt.congr_deriv (hode t)
  exact ((hDD.div_const 2).add
    (((radialForce_hasDerivAt (v t)).comp t hD).const_mul σ)).deriv

private theorem exp_mul_hasDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c t : ℝ) :
    HasDerivAt (fun s => Real.exp (c * s) * f s)
      (Real.exp (c * t) * (c * f t + deriv f t)) t := by
  have hE := ((hasDerivAt_id t).const_mul c).exp
  have hF := (hf.differentiable (by simp) t).hasDerivAt
  apply (hE.mul hF).congr_deriv
  simp only [id_eq]
  ring

private theorem exp_mul_second {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c t : ℝ) :
    deriv (deriv (fun s => Real.exp (c * s) * f s)) t =
      Real.exp (c * t) * (deriv (deriv f) t + 2 * c * deriv f t + c ^ 2 * f t) := by
  have hfirst : deriv (fun s => Real.exp (c * s) * f s) =
      fun s => Real.exp (c * s) * (c * f s + deriv f s) :=
    funext fun s => (exp_mul_hasDerivAt hf c s).deriv
  rw [hfirst]
  have hE := ((hasDerivAt_id t).const_mul c).exp
  have hF := (hf.differentiable (by simp) t).hasDerivAt
  have hD := ((smooth_deriv hf).differentiable (by simp) t).hasDerivAt
  apply HasDerivAt.deriv
  apply (hE.mul ((hF.const_mul c).add hD)).congr_deriv
  simp only [id_eq, Pi.add_apply]
  ring

theorem translationMode_contDiff {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (σ : ℝ) :
    ContDiff ℝ ∞ (translationMode v σ) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (modeFlux_contDiff hv σ)

theorem translationMode_deriv {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hode : ∀ t, deriv (deriv v) t = radialForce (v t)) (σ t : ℝ) :
    deriv (translationMode v σ) t = Real.exp (σ * t) *
      (σ * modeFlux v σ t + deriv v t / 2 + σ * radialForce (v t)) := by
  have h := (exp_mul_hasDerivAt (modeFlux_contDiff hv σ) σ t).deriv
  rw [(modeFlux_hasDerivAt hv hode σ t).deriv] at h
  exact h.trans (by ring)

/-- The first spherical eigenvalue in dimension three is 2. The two actual
modes solve this scalar mode equation with that normalization. -/
theorem translationMode_jacobi {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hode : ∀ t, deriv (deriv v) t = radialForce (v t))
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) :
    modelJacobi v 2 (translationMode v σ) t = 0 := by
  unfold modelJacobi
  change deriv (deriv (fun s => Real.exp (σ * s) * modeFlux v σ s)) t - _ + _ = 0
  rw [exp_mul_second (modeFlux_contDiff hv σ), modeFlux_second hv hode,
    (modeFlux_hasDerivAt hv hode σ t).deriv]
  unfold translationMode modeFlux radialForce
  rcases hσ with rfl | rfl <;> ring

theorem modeFlux_pos {v : ℝ → ℝ} {t σ : ℝ}
    (hb : |deriv v t| < v t / 2) (hσ : σ = 1 ∨ σ = -1) : 0 < modeFlux v σ t := by
  have h := abs_lt.mp hb
  unfold modeFlux
  rcases hσ with rfl | rfl <;> linarith

theorem translationMode_pos {v : ℝ → ℝ} {t σ : ℝ}
    (hb : |deriv v t| < v t / 2) (hσ : σ = 1 ∨ σ = -1) :
    0 < translationMode v σ t := mul_pos (Real.exp_pos _) (modeFlux_pos hb hσ)

/-- The exact positive flux identity, with the normalized energy q. -/
theorem modeFlux_product {v : ℝ → ℝ} {t q : ℝ}
    (he : 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = -q) :
    modeFlux v (-1) t * modeFlux v 1 t = (v t ^ 6 + q) / 4 := by
  unfold modeFlux
  nlinarith

/-- Uniform flux lower bounds retain the small energy q explicitly. -/
theorem modeFlux_lower_bound {v : ℝ → ℝ} {t q : ℝ}
    (hv : 0 < v t) (hb : |deriv v t| < v t / 2)
    (he : 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = -q) :
    q / 4 ≤ v t * modeFlux v (-1) t ∧ q / 4 ≤ v t * modeFlux v 1 t := by
  have hJ := modeFlux_pos hb (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
  have hK := modeFlux_pos hb (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
  have hprod := modeFlux_product he
  have hbound := abs_lt.mp hb
  have hJu : modeFlux v (-1) t ≤ v t := by unfold modeFlux; linarith
  have hKu : modeFlux v 1 t ≤ v t := by unfold modeFlux; linarith
  have hpow := pow_nonneg hv.le 6
  constructor
  · have h := mul_le_mul_of_nonneg_left hKu hJ.le
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hJu hK.le
    nlinarith

/-- The actual Wronskian of the two first modes is nonzero at negative energy. -/
theorem translationMode_wronskian {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hode : ∀ t, deriv (deriv v) t = radialForce (v t)) {q : ℝ}
    (he : ∀ t, 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = -q) (t : ℝ) :
    translationMode v 1 t * deriv (translationMode v (-1)) t -
      translationMode v (-1) t * deriv (translationMode v 1) t = -3 * q / 4 := by
  rw [translationMode_deriv hv hode, translationMode_deriv hv hode]
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = (Real.exp t * Real.exp (-t)) *
        (3 * deriv v t ^ 2 + 3 / 4 * v t ^ 6 - 3 / 4 * v t ^ 2) := by
      unfold translationMode modeFlux radialForce
      simp only [one_mul, neg_one_mul]
      ring
    _ = _ := by rw [hexp]; nlinarith [he t]

/-- The displayed periodic orbit and its positive first-mode fundamental
pair are constructed from ε,e alone. No mode existence or inverse is assumed. -/
theorem exists_delaunay_with_first_modes {ε e : ℝ}
    (hε : 0 < ε) (he : 0 < e) (hsmall : ε ^ 2 * e < 3 / 8) :
    ∃ (v : ℝ → ℝ) (T : ℝ),
      0 < T ∧ ContDiff ℝ ∞ v ∧ Function.Periodic v T ∧
      (∀ t, ε * Real.sqrt e ≤ v t ∧ v t < 1) ∧
      (∀ t, deriv (deriv v) t = radialForce (v t)) ∧
      (∀ t, 4 * deriv v t ^ 2 + v t ^ 6 - v t ^ 2 = -(ε ^ 2 * e)) ∧
      (∀ t, modelJacobi v 0 (deriv v) t = 0) ∧
      (∀ σ, σ = 1 ∨ σ = -1 → ContDiff ℝ ∞ (translationMode v σ) ∧
        (∀ t, 0 < translationMode v σ t) ∧
        (∀ t, modelJacobi v 2 (translationMode v σ) t = 0)) ∧
      (∀ t, translationMode v 1 t * deriv (translationMode v (-1)) t -
        translationMode v (-1) t * deriv (translationMode v 1) t = -3 * (ε ^ 2 * e) / 4) ∧
      (∀ t, ε ^ 2 * e / 4 ≤ v t * modeFlux v (-1) t ∧
        ε ^ 2 * e / 4 ≤ v t * modeFlux v 1 t) := by
  obtain ⟨η, v, T, hη, _, hηlow, _, hT, hs, hp, hb, _, _, _, hode, henergy, hder, _⟩ :=
    exists_delaunay_energy_parameters hε he hsmall
  refine ⟨v, T, hT, hs, hp, ?_, hode, henergy, phase_mode_jacobi hs hode, ?_,
    translationMode_wronskian hs hode henergy, ?_⟩
  · intro t
    exact ⟨hηlow.trans (hb t).1, (hb t).2⟩
  · intro σ hσ
    exact ⟨translationMode_contDiff hs σ,
      fun t => translationMode_pos (hder t) hσ,
      translationMode_jacobi hs hode hσ⟩
  · intro t
    exact modeFlux_lower_bound (hη.trans_le (hb t).1) (hder t) (henergy t)

#print axioms phase_mode_jacobi
#print axioms translationMode_jacobi
#print axioms translationMode_wronskian
#print axioms exists_delaunay_with_first_modes

end Yamabe3.Analysis.Delaunay
