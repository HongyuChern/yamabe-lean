import Yamabe3.Analysis.UniformElliptic.NativeC1StrongLimit

/-!
# Energy and weak equations of the same strong H1 limit

All pairings retain the original functions and measure. The potential is
required only to give L2 products with the actual compact tests; no global
boundedness near a puncture is assumed. The forcing factor is exactly 1/8,
as in the normalized physical Yamabe Jacobi equation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

variable {ι X : Type*} [MeasurableSpace X]

theorem native_integral_toLp_mul {μ : Measure X} {f : X → ℝ}
    (hf : MemLp f 2 μ) (ψ : X → ℝ) :
    (∫ x, hf.toLp f x * ψ x ∂μ) = ∫ x, f x * ψ x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- L2 pairing continuity written using the original approximating
functions and the actual constructed limit class. -/
theorem native_tendsto_integral_mul_of_toLp_tendsto
    {l : Filter ι} {μ : Measure X} {v : ι → X → ℝ} {g : Lp ℝ 2 μ}
    (hv : ∀ a, MemLp (v a) 2 μ)
    (hlim : Tendsto (fun a => (hv a).toLp (v a)) l (𝓝 g))
    {ψ : X → ℝ} (hψ : MemLp ψ 2 μ) :
    Tendsto (fun a => ∫ x, v a x * ψ x ∂μ) l (𝓝 (∫ x, g x * ψ x ∂μ)) := by
  simpa only [native_integral_toLp_mul] using
    native_tendsto_integral_mul_L2_filter hlim hψ

/-- Square-integral convergence gives pairing convergence to the
specified original function, not to an unidentified representative. -/
theorem native_tendsto_integral_mul_of_integral_sq_sub
    {l : Filter ι} {μ : Measure X} {v : ι → X → ℝ} {u : X → ℝ}
    (hv : ∀ a, MemLp (v a) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun a => ∫ x, (v a x - u x) ^ 2 ∂μ) l (𝓝 0))
    {ψ : X → ℝ} (hψ : MemLp ψ 2 μ) :
    Tendsto (fun a => ∫ x, v a x * ψ x ∂μ) l (𝓝 (∫ x, u x * ψ x ∂μ)) := by
  simpa only [native_integral_toLp_mul] using
    native_tendsto_integral_mul_L2_filter
      (native_tendsto_toLp_of_integral_sq_sub_filter hv hu hlim) hψ

/-- Strong L2 convergence preserves the actual quadratic energy. -/
theorem native_tendsto_integral_sq_of_toLp_tendsto
    {l : Filter ι} {μ : Measure X} {v : ι → X → ℝ} {g : Lp ℝ 2 μ}
    (hv : ∀ a, MemLp (v a) 2 μ)
    (hlim : Tendsto (fun a => (hv a).toLp (v a)) l (𝓝 g)) :
    Tendsto (fun a => ∫ x, v a x ^ 2 ∂μ) l (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
  have h := hlim.norm.pow 2
  have hg : ‖g‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    simpa only [Lp.toLp_coeFn] using native_norm_toLp_sq_eq_integral_sq (Lp.memLp g)
  simpa only [native_norm_toLp_sq_eq_integral_sq, hg] using h

/-- The finite sum of actual first-derivative energies converges. -/
theorem native_tendsto_gradient_energy_of_toLp_tendsto
    {l : Filter ι} {μ : Measure X} {I : Type*} [Fintype I]
    {v : ι → I → X → ℝ} {g : I → Lp ℝ 2 μ}
    (hv : ∀ a i, MemLp (v a i) 2 μ)
    (hlim : ∀ i, Tendsto (fun a => (hv a i).toLp (v a i)) l (𝓝 (g i))) :
    Tendsto (fun a => ∫ x, ∑ i : I, v a i x ^ 2 ∂μ)
      l (𝓝 (∫ x, ∑ i : I, g i x ^ 2 ∂μ)) := by
  classical
  have hsum := tendsto_finsetSum Finset.univ
    (fun i _ => native_tendsto_integral_sq_of_toLp_tendsto (fun a => hv a i) (hlim i))
  have hs (a : ι) : (∫ x, ∑ i : I, v a i x ^ 2 ∂μ) =
      ∑ i : I, ∫ x, v a i x ^ 2 ∂μ :=
    integral_finsetSum Finset.univ (fun i _ => (hv a i).integrable_sq)
  have hg : (∫ x, ∑ i : I, g i x ^ 2 ∂μ) =
      ∑ i : I, ∫ x, g i x ^ 2 ∂μ :=
    integral_finsetSum Finset.univ (fun i _ => (Lp.memLp (g i)).integrable_sq)
  simpa only [hs, hg] using hsum

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The normalized physical equation passes to the same L2 value and
the same strongly convergent gradient. Potential integrability is local
to each actual test. The coefficient 1/8 is retained exactly. -/
theorem native_weak_equation_of_strong_L2_limits
    {l : Filter ι} [NeBot l] {Ω : Set E}
    {uSeq fSeq : ι → E → ℝ} {u f C : E → ℝ}
    (hval : ∀ a, MemLp (uSeq a) 2 (volume.restrict Ω))
    (hu : MemLp u 2 (volume.restrict Ω))
    (hsource : ∀ a, MemLp (fSeq a) 2 (volume.restrict Ω))
    (hf : MemLp f 2 (volume.restrict Ω))
    (hlimu : Tendsto (fun a => ∫ x in Ω, (uSeq a x - u x) ^ 2) l (𝓝 0))
    (hlimf : Tendsto (fun a => ∫ x in Ω, (fSeq a x - f x) ^ 2) l (𝓝 0))
    (vSeq : ι → Fin d → E → ℝ)
    (hv : ∀ a i, MemLp (vSeq a i) 2 (volume.restrict Ω))
    (du : Fin d → Lp ℝ 2 (volume.restrict Ω))
    (hdu : ∀ i, Tendsto (fun a => (hv a i).toLp (vSeq a i)) l (𝓝 (du i)))
    (hCtest : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      MemLp (fun x => C x * φ x) 2 (volume.restrict Ω))
    (heq : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, vSeq a i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (∫ x in Ω, fSeq a x * φ x) / 8 + ∫ x in Ω, uSeq a x * (C x * φ x)) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (∫ x in Ω, f x * φ x) / 8 + ∫ x in Ω, u x * (C x * φ x) := by
  classical
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hdφLp (i : Fin d) : MemLp
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).restrict Ω
  have hleft := tendsto_finsetSum Finset.univ
    (fun i _ => native_tendsto_integral_mul_of_toLp_tendsto
      (fun a => hv a i) (hdu i) (hdφLp i))
  have hsSeq (a : ι) :
      (∫ x in Ω, ∑ i : Fin d, vSeq a i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∑ i : Fin d, ∫ x in Ω, vSeq a i x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    integral_finsetSum Finset.univ (fun i _ => (hv a i).integrable_mul (hdφLp i))
  have hsLim :
      (∫ x in Ω, ∑ i : Fin d, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∑ i : Fin d, ∫ x in Ω, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    integral_finsetSum Finset.univ (fun i _ => (Lp.memLp (du i)).integrable_mul (hdφLp i))
  have hleft' : Tendsto
      (fun a => ∫ x in Ω, ∑ i : Fin d, vSeq a i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) l
      (𝓝 (∫ x in Ω, ∑ i : Fin d, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    simpa only [hsSeq, hsLim] using hleft
  have hright := ((native_tendsto_integral_mul_of_integral_sq_sub hsource hf hlimf hφLp).div_const 8).add
    (native_tendsto_integral_mul_of_integral_sq_sub hval hu hlimu (hCtest φ hφ hc hs))
  exact tendsto_nhds_unique hleft'
    (hright.congr' (Eventually.of_forall fun a => (heq a φ hφ hc hs).symm))

/-- One consumer constructs actual H1 derivatives, retains their strong
convergence and energy limit, and passes the original normalized equation
to the same specified physical function and source. -/
theorem native_C1_same_value_weak_equation_limit
    [Nonempty ι] [SemilatticeSup ι] {Ω : Set E} (hΩ : IsOpen Ω)
    {u f C : E → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hf : MemLp f 2 (volume.restrict Ω))
    (uSeq fSeq : ι → E → ℝ)
    (hC1 : ∀ a, ContDiffOn ℝ 1 (uSeq a) Ω)
    (hval : ∀ a, MemLp (uSeq a) 2 (volume.restrict Ω))
    (hsource : ∀ a, MemLp (fSeq a) 2 (volume.restrict Ω))
    (hder : ∀ a (i : Fin d), MemLp
      (fun x => fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω))
    (hlimu : Tendsto (fun a => ∫ x in Ω, (uSeq a x - u x) ^ 2) atTop (𝓝 0))
    (hlimf : Tendsto (fun a => ∫ x in Ω, (fSeq a x - f x) ^ 2) atTop (𝓝 0))
    (hgrad : Tendsto (fun ab : ι × ι => ∫ x in Ω, ∑ i : Fin d,
      (fderiv ℝ (uSeq ab.1) x (EuclideanSpace.single i 1) -
        fderiv ℝ (uSeq ab.2) x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0))
    (hCtest : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      MemLp (fun x => C x * φ x) 2 (volume.restrict Ω))
    (heq : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d,
        fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (∫ x in Ω, fSeq a x * φ x) / 8 + ∫ x in Ω, uSeq a x * (C x * φ x)) :
    Poincare.Analysis.Sobolev.Weak.MemH1 u Ω ∧
    ∃ du : Fin d → Lp ℝ 2 (volume.restrict Ω),
      (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u Ω) ∧
      Tendsto (fun a => ∫ x in Ω, (uSeq a x - u x) ^ 2 + ∑ i : Fin d,
        (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) - du i x) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun a => ∫ x in Ω, ∑ i : Fin d,
        (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1)) ^ 2)
        atTop (𝓝 (∫ x in Ω, ∑ i : Fin d, du i x ^ 2)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        (∫ x in Ω, ∑ i : Fin d, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x in Ω, f x * φ x) / 8 + ∫ x in Ω, u x * (C x * φ x)) := by
  obtain ⟨hH1, du, hweak, hdu, htotal⟩ :=
    native_exists_strong_weak_partials_of_C1_cauchy hΩ hu uSeq hC1 hval hder hlimu hgrad
  refine ⟨hH1, du, hweak, htotal,
    native_tendsto_gradient_energy_of_toLp_tendsto hder hdu, ?_⟩
  exact native_weak_equation_of_strong_L2_limits hval hu hsource hf hlimu hlimf
    (fun a i x => fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1)) hder du hdu hCtest heq

#print axioms native_tendsto_integral_sq_of_toLp_tendsto
#print axioms native_tendsto_gradient_energy_of_toLp_tendsto
#print axioms native_weak_equation_of_strong_L2_limits
#print axioms native_C1_same_value_weak_equation_limit

end Yamabe3.Analysis.UniformElliptic
