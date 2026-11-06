import Yamabe3.Analysis.UniformElliptic.NativeC1Caccioppoli
import Yamabe3.Analysis.UniformElliptic.NativeH1EquationLimit

/-!
# Same-function local strong H1 closure from the actual equation

The approximating fields are only C1. Their values and physical sources
converge in L2 on a larger open region. One fixed compact smooth cutoff
and the original same-potential weak equation then produce the missing
two-index gradient estimate on a smaller open region. The conclusion is
native H1 membership, strong H1 convergence, convergence of the actual
gradient energy, and the original normalized equation for the specified
function and source.

No gradient-Cauchy hypothesis, subsequence, zero trace of the solution,
or conclusion-shaped certificate is an input. The individual classical
gradients must be in L2 on the larger region. A singular physical
potential is only required to be bounded on that fixed larger region;
this is a local theorem and does not assert a global bound at a puncture.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.UniformElliptic

variable {ι X : Type*} [MeasurableSpace X]

/-- Convergence of the actual square errors gives two-index convergence
of the actual square differences, for the original directed net. -/
theorem native_integral_sq_cauchy_of_limit
    [Nonempty ι] [SemilatticeSup ι] {μ : Measure X}
    {v : ι → X → ℝ} {u : X → ℝ}
    (hv : ∀ a, MemLp (v a) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun a => ∫ x, (v a x - u x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun ab : ι × ι => ∫ x, (v ab.1 x - v ab.2 x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hLp := native_tendsto_toLp_of_integral_sq_sub_filter hv hu hlim
  have hd := cauchySeq_iff_tendsto_dist_atTop_0.mp hLp.cauchySeq
  simpa only [dist_eq_norm, native_norm_toLp_sub_sq_eq_integral_sq,
    zero_pow (by decide : (2 : ℕ) ≠ 0)] using hd.pow 2

/-- Square-error convergence restricts to any smaller measurable region
without changing the original functions. -/
theorem native_tendsto_integral_sq_sub_restrict
    {l : Filter ι} {μ : Measure X} {W Ω : Set X} (hWΩ : W ⊆ Ω)
    {v : ι → X → ℝ} {u : X → ℝ}
    (hv : ∀ a, MemLp (v a) 2 (μ.restrict Ω)) (hu : MemLp u 2 (μ.restrict Ω))
    (hlim : Tendsto (fun a => ∫ x in Ω, (v a x - u x) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun a => ∫ x in W, (v a x - u x) ^ 2 ∂μ) l (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
    (fun a => setIntegral_mono_set ((hv a).sub hu).integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun x => @hWΩ x)) hlim

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Continuity on a neighborhood of the compact closure supplies the
actual L2 value on the integration region. -/
theorem native_memLp_two_of_continuousOn_precompact
    {O Ω : Set E} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩO : closure Ω ⊆ O) {v : E → ℝ} (hv : ContinuousOn v O) :
    MemLp v 2 (volume.restrict Ω) := by
  have hm : AEStronglyMeasurable v (volume.restrict Ω) :=
    (hv.mono (subset_closure.trans hΩO)).aestronglyMeasurable hΩ
  apply (memLp_two_iff_integrable_sq hm).mpr
  exact (((hv.mono hΩO).pow 2).integrableOn_compact hΩc).mono_set subset_closure

/-- C1 regularity on the larger neighborhood supplies L2 integrability
of each actual classical partial on the compactly contained region.
There is no bound uniform in an approximating family in this assertion. -/
theorem native_C1_partials_memLp_on_precompact
    {O Ω : Set E} (hO : IsOpen O) (hΩ : MeasurableSet Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O)
    {v : E → ℝ} (hv : ContDiffOn ℝ 1 v O) (i : Fin d) :
    MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) :=
  native_memLp_two_of_continuousOn_precompact hΩ hΩc hΩO
    ((hv.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const)

private theorem local_setIntegral_eq {W Ω : Set E} (hWΩ : W ⊆ Ω)
    {g : E → ℝ} (hg : ∀ x, x ∉ W → g x = 0) :
    (∫ x in W, g x) = ∫ x in Ω, g x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hg,
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hg x (fun hxW => hx (hWΩ hxW)))]

private theorem local_bounded_mul_memLp {μ : Measure E} {Q v : E → ℝ} {A : ℝ}
    (hQ : AEStronglyMeasurable Q μ) (hbound : ∀ᵐ x ∂μ, ‖Q x‖ ≤ A)
    (hv : MemLp v 2 μ) : MemLp (fun x => Q x * v x) 2 μ := by
  apply hv.of_le_mul (c := A) (hQ.mul hv.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖Q x * v x‖ ≤ A * ‖v x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- The local strong-H1 and PDE limit theorem has only value/source
convergence inputs: its gradient convergence is proved by Caccioppoli
for the original C1 fields and their original same-potential equations. -/
theorem native_C1_local_strong_equation_of_value_source_limits
    [Nonempty ι] [SemilatticeSup ι]
    {Ω W : Set E} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηone : ∀ x ∈ W, η x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hDη : ∀ x (i : Fin d), |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B)
    {u f Q : E → ℝ} {A : ℝ}
    (hQ : AEStronglyMeasurable Q (volume.restrict Ω))
    (hQbound : ∀ᵐ x ∂(volume.restrict Ω), ‖Q x‖ ≤ A)
    (hu : MemLp u 2 (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (uSeq fSeq : ι → E → ℝ)
    (hC1 : ∀ a, ContDiffOn ℝ 1 (uSeq a) Ω)
    (hval : ∀ a, MemLp (uSeq a) 2 (volume.restrict Ω))
    (hsource : ∀ a, MemLp (fSeq a) 2 (volume.restrict Ω))
    (hder : ∀ a (i : Fin d), MemLp
      (fun x => fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω))
    (hlimu : Tendsto (fun a => ∫ x in Ω, (uSeq a x - u x) ^ 2) atTop (𝓝 0))
    (hlimf : Tendsto (fun a => ∫ x in Ω, (fSeq a x - f x) ^ 2) atTop (𝓝 0))
    (heq : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d,
        fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, (fSeq a x / 8 + Q x * uSeq a x) * φ x) :
    Poincare.Analysis.Sobolev.Weak.MemH1 u W ∧
    ∃ du : Fin d → Lp ℝ 2 (volume.restrict W),
      (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u W) ∧
      Tendsto (fun a => ∫ x in W, (uSeq a x - u x) ^ 2 + ∑ i : Fin d,
        (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) - du i x) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun a => ∫ x in W, ∑ i : Fin d,
        (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1)) ^ 2)
        atTop (𝓝 (∫ x in W, ∑ i : Fin d, du i x ^ 2)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
        (∫ x in W, ∑ i : Fin d, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x in W, f x * φ x) / 8 + ∫ x in W, u x * (Q x * φ x)) := by
  have hgrad := native_C1_gradient_cauchy_of_fixed_potential
    (u := uSeq) (f := fSeq) (Q := Q) (C := A)
    hΩ hW.measurableSet hWΩ hη hηc hηΩ hηrange hηone hB hDη hQ hQbound
    hC1 hval hsource hder heq
    (native_integral_sq_cauchy_of_limit hval hu hlimu)
    (native_integral_sq_cauchy_of_limit hsource hf hlimf)
  have hμ : volume.restrict W ≤ volume.restrict Ω := Measure.restrict_mono hWΩ le_rfl
  have hvalW (a : ι) : MemLp (uSeq a) 2 (volume.restrict W) := (hval a).mono_measure hμ
  have hsourceW (a : ι) : MemLp (fSeq a) 2 (volume.restrict W) := (hsource a).mono_measure hμ
  have hQW := hQ.mono_measure hμ
  have hQboundW := ae_mono hμ hQbound
  have hQtest (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
      (_hs : tsupport φ ⊆ W) : MemLp (fun x => Q x * φ x) 2 (volume.restrict W) :=
    local_bounded_mul_memLp hQW hQboundW
      ((hφ.continuous.memLp_of_hasCompactSupport hc).restrict W)
  apply native_C1_same_value_weak_equation_limit hW (hu.mono_measure hμ) (hf.mono_measure hμ)
    uSeq fSeq (fun a => (hC1 a).mono hWΩ) hvalW hsourceW
    (fun a i => (hder a i).mono_measure hμ)
    (native_tendsto_integral_sq_sub_restrict hWΩ hval hu hlimu)
    (native_tendsto_integral_sq_sub_restrict hWΩ hsource hf hlimf) hgrad hQtest
  intro a φ hφ hc hs
  have hleft := local_setIntegral_eq hWΩ (g := fun x => ∑ i : Fin d,
    fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) (fun x hx => by
        apply Finset.sum_eq_zero
        intro i _hi
        rw [image_eq_zero_of_notMem_tsupport
          (fun ht => hx (hs (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) ht))),
          mul_zero])
  have hright := local_setIntegral_eq hWΩ
    (g := fun x => (fSeq a x / 8 + Q x * uSeq a x) * φ x) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero])
  have hφLp : MemLp φ 2 (volume.restrict W) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict W
  have hfi : Integrable (fun x => fSeq a x * φ x) (volume.restrict W) :=
    (hsourceW a).integrable_mul hφLp
  have hui : Integrable (fun x => uSeq a x * (Q x * φ x)) (volume.restrict W) :=
    (hvalW a).integrable_mul (hQtest φ hφ hc hs)
  calc
    _ = ∫ x in W, (fSeq a x / 8 + Q x * uSeq a x) * φ x := by
      rw [hleft, hright]
      exact heq a φ hφ hc (hs.trans hWΩ)
    _ = ∫ x in W, (fSeq a x * φ x) / 8 + uSeq a x * (Q x * φ x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    _ = _ := by
      rw [integral_add (hfi.div_const 8) hui, integral_div]

/-- On a compactly contained larger region, the C1 regularity supplies
all individual value and gradient L2 hypotheses used by the local
theorem. Only the physical sources retain their explicit L2 assumption. -/
theorem native_C1_local_strong_equation_on_precompact
    [Nonempty ι] [SemilatticeSup ι]
    {O Ω W : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O)
    (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηone : ∀ x ∈ W, η x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hDη : ∀ x (i : Fin d), |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ B)
    {u f Q : E → ℝ} {A : ℝ}
    (hQ : AEStronglyMeasurable Q (volume.restrict Ω))
    (hQbound : ∀ᵐ x ∂(volume.restrict Ω), ‖Q x‖ ≤ A)
    (hu : MemLp u 2 (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (uSeq fSeq : ι → E → ℝ)
    (hC1 : ∀ a, ContDiffOn ℝ 1 (uSeq a) O)
    (hsource : ∀ a, MemLp (fSeq a) 2 (volume.restrict Ω))
    (hlimu : Tendsto (fun a => ∫ x in Ω, (uSeq a x - u x) ^ 2) atTop (𝓝 0))
    (hlimf : Tendsto (fun a => ∫ x in Ω, (fSeq a x - f x) ^ 2) atTop (𝓝 0))
    (heq : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, ∑ i : Fin d,
        fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in Ω, (fSeq a x / 8 + Q x * uSeq a x) * φ x) :
    Poincare.Analysis.Sobolev.Weak.MemH1 u W ∧
    ∃ du : Fin d → Lp ℝ 2 (volume.restrict W),
      (∀ i, Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i (du i) u W) ∧
      Tendsto (fun a => ∫ x in W, (uSeq a x - u x) ^ 2 + ∑ i : Fin d,
        (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1) - du i x) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun a => ∫ x in W, ∑ i : Fin d,
        (fderiv ℝ (uSeq a) x (EuclideanSpace.single i 1)) ^ 2)
        atTop (𝓝 (∫ x in W, ∑ i : Fin d, du i x ^ 2)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
        (∫ x in W, ∑ i : Fin d, du i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          (∫ x in W, f x * φ x) / 8 + ∫ x in W, u x * (Q x * φ x)) := by
  exact native_C1_local_strong_equation_of_value_source_limits
    hΩ hW hWΩ hη hηc hηΩ hηrange hηone hB hDη hQ hQbound hu hf uSeq fSeq
    (fun a => (hC1 a).mono (subset_closure.trans hΩO))
    (fun a => native_memLp_two_of_continuousOn_precompact hΩ.measurableSet hΩc hΩO
      (hC1 a).continuousOn) hsource
    (fun a i => native_C1_partials_memLp_on_precompact hO hΩ.measurableSet hΩc hΩO (hC1 a) i)
    hlimu hlimf heq

#print axioms native_integral_sq_cauchy_of_limit
#print axioms native_tendsto_integral_sq_sub_restrict
#print axioms native_memLp_two_of_continuousOn_precompact
#print axioms native_C1_partials_memLp_on_precompact
#print axioms native_C1_local_strong_equation_of_value_source_limits
#print axioms native_C1_local_strong_equation_on_precompact

end Yamabe3.Analysis.UniformElliptic
