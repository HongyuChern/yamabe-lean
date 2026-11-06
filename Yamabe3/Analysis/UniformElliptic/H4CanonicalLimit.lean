import Yamabe3.Analysis.UniformElliptic.LocalH4CauchyLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Identifying the local H4 limit with the original canonical L2 value

The C2 function is constructed from the actual smooth H4-Cauchy sequence.
Its equality almost everywhere with a preassigned L2 limit is proved by
extracting an almost-everywhere convergent subsequence of that same sequence.
No L2 property of the new representative is assumed. The measure in the
identification is an arbitrary fixed measure, so it may be the original
native Riemannian volume; no silent change to Euclidean volume occurs.

For a measure positive on nonempty open sets, a preassigned continuous
canonical representative is itself C2 and has the actual derivative limits.
Local representatives from different domains agree, with all their germs,
on the overlap. No coupled inverse or new solution is constructed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic.InteriorEstimates

/-- L2 convergence and almost-everywhere pointwise convergence of the same
sequence have the same limit. The pointwise limit is not assumed L2. -/
theorem ae_eq_of_l2_limit_of_ae_pointwise_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : ℕ → α → ℝ} {U W : α → ℝ}
    (hu : ∀ n, AEStronglyMeasurable (u n) μ)
    (hW : AEStronglyMeasurable W μ)
    (hL2 : Tendsto (fun n => eLpNorm (fun x => u n x - W x) 2 μ)
      atTop (𝓝 0))
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (U x))) :
    U =ᵐ[μ] W := by
  have hmeasure : TendstoInMeasure μ u atTop W :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      hu hW hL2
  obtain ⟨σ, hσ, hsub⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hpoint, hsub] with x hUx hWx
  exact tendsto_nhds_unique (hUx.comp hσ.tendsto_atTop) hWx

/-- A genuine L2-class convergence can be consumed directly, while every
pointwise approximant remains the given representative of that same class.
The identification is local and does not assume a finite measure. -/
theorem ae_eq_on_of_tendsto_Lp_of_ae_representatives
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Ω : Set α} (hΩ : MeasurableSet Ω)
    (z : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hz : Tendsto z atTop (𝓝 Z)) (u : ℕ → α → ℝ) (U : α → ℝ)
    (hrep : ∀ n, u n =ᵐ[μ.restrict Ω] (z n : α → ℝ))
    (hpoint : ∀ x ∈ Ω, Tendsto (fun n => u n x) atTop (𝓝 (U x))) :
    U =ᵐ[μ.restrict Ω] (Z : α → ℝ) := by
  obtain ⟨σ, hσ, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hz).exists_seq_tendsto_ae
  have hrepAll : ∀ᵐ x ∂μ.restrict Ω, ∀ n, u n x = z n x := ae_all_iff.mpr hrep
  filter_upwards [hrepAll, ae_restrict_of_ae hsub, ae_restrict_mem hΩ] with x hx hZx hxΩ
  have hUx := (hpoint x hxΩ).comp hσ.tendsto_atTop
  have heq : (fun n => u (σ n) x) = (fun n => z (σ n) x) :=
    funext fun n => hx (σ n)
  change Tendsto (fun n => u (σ n) x) atTop (𝓝 (U x)) at hUx
  rw [heq] at hUx
  exact tendsto_nhds_unique hUx hZx

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Pointwise convergence on the actual open region identifies the L2
limit for the same restricted measure, including native volume measures. -/
theorem ae_eq_of_l2_limit_of_pointwise_limit_on_open
    (μ : Measure E3) {O : Set E3} (hO : IsOpen O)
    {u : ℕ → E3 → ℝ} {U W : E3 → ℝ}
    (hu : ∀ n, ContinuousOn (u n) O)
    (hW : AEStronglyMeasurable W (μ.restrict O))
    (hL2 : Tendsto (fun n => eLpNorm (fun x => u n x - W x) 2 (μ.restrict O))
      atTop (𝓝 0))
    (hpoint : ∀ x ∈ O, Tendsto (fun n => u n x) atTop (𝓝 (U x))) :
    U =ᵐ[μ.restrict O] W := by
  apply ae_eq_of_l2_limit_of_ae_pointwise_limit
    (fun n => (hu n).aestronglyMeasurable hO.measurableSet) hW hL2
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  exact hpoint x hx

/-- The actual H4-Cauchy construction gives a C2 representative of the
preassigned L2 limit, rather than a separately chosen solution class. -/
theorem exists_same_c2_canonical_limit_of_locally_h4_cauchy
    (μ : Measure E3) {O : Set E3} (hO : IsOpen O)
    (u : ℕ → E3 → ℝ) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) O)
    (hCauchy : ∀ V : Set E3, IsOpen V → IsCompact (closure V) → closure V ⊆ O →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        (derivativeProfile 2 V 4 (fun x => u n x - u m x)).toReal ≤ ε)
    (W : E3 → ℝ) (hW : AEStronglyMeasurable W (μ.restrict O))
    (hL2 : Tendsto (fun n => eLpNorm (fun x => u n x - W x) 2 (μ.restrict O))
      atTop (𝓝 0)) :
    ∃ U : E3 → ℝ, ContDiffOn ℝ 2 U O ∧ U =ᵐ[μ.restrict O] W ∧
      (∀ x ∈ O, Tendsto (fun n => u n x) atTop (𝓝 (U x)) ∧
        ∀ j ≤ 2, Tendsto (fun n => iteratedFDeriv ℝ j (u n) x)
          atTop (𝓝 (iteratedFDeriv ℝ j U x))) ∧
      (∀ V : E3 → ℝ,
        (∀ x ∈ O, Tendsto (fun n => u n x) atTop (𝓝 (V x))) → EqOn U V O) := by
  obtain ⟨U, hU, hjet, huniq⟩ :=
    exists_same_c2_limit_of_locally_h4_cauchy hO u hu hCauchy
  refine ⟨U, hU, ?_, hjet, huniq⟩
  exact ae_eq_of_l2_limit_of_pointwise_limit_on_open μ hO
    (fun n => (hu n).continuousOn) hW hL2 (fun x hx => (hjet x hx).1)

/-- If the canonical value was already selected continuously, it is that
literal function which is C2 and whose actual derivatives are the limits. -/
theorem contDiffOn_two_canonical_of_locally_h4_cauchy
    (μ : Measure E3) [μ.IsOpenPosMeasure] {O : Set E3} (hO : IsOpen O)
    (u : ℕ → E3 → ℝ) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) O)
    (hCauchy : ∀ V : Set E3, IsOpen V → IsCompact (closure V) → closure V ⊆ O →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        (derivativeProfile 2 V 4 (fun x => u n x - u m x)).toReal ≤ ε)
    (W : E3 → ℝ) (hW : ContinuousOn W O)
    (hL2 : Tendsto (fun n => eLpNorm (fun x => u n x - W x) 2 (μ.restrict O))
      atTop (𝓝 0)) :
    ContDiffOn ℝ 2 W O ∧
      ∀ x ∈ O, Tendsto (fun n => u n x) atTop (𝓝 (W x)) ∧
        ∀ j ≤ 2, Tendsto (fun n => iteratedFDeriv ℝ j (u n) x)
          atTop (𝓝 (iteratedFDeriv ℝ j W x)) := by
  obtain ⟨U, hU, hUae, hjet, _⟩ :=
    exists_same_c2_canonical_limit_of_locally_h4_cauchy μ hO u hu hCauchy W
      (hW.aestronglyMeasurable hO.measurableSet) hL2
  have heq : EqOn U W O := Measure.eqOn_open_of_ae_eq hUae hO hU.continuousOn hW
  have hgerm (x : E3) (hx : x ∈ O) : U =ᶠ[𝓝 x] W := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact heq hy
  refine ⟨?_, ?_⟩
  · intro x hx
    exact ((hU.contDiffAt (hO.mem_nhds hx)).congr_of_eventuallyEq
      (hgerm x hx).symm).contDiffWithinAt
  · intro x hx
    refine ⟨?_, ?_⟩
    · simpa only [heq hx] using (hjet x hx).1
    · intro j hj
      have he : iteratedFDeriv ℝ j U x = iteratedFDeriv ℝ j W x :=
        ((hgerm x hx).iteratedFDeriv ℝ j).self_of_nhds
      simpa only [he] using (hjet x hx).2 j hj

/-- Continuous representatives of the same fixed function agree on the
overlap of two open regions, with all local germs and actual derivatives.
No matching condition is inserted as a hypothesis. -/
theorem canonical_local_representatives_compatible
    (μ : Measure E3) [μ.IsOpenPosMeasure]
    {O₁ O₂ : Set E3} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {U₁ U₂ W : E3 → ℝ} (hU₁ : ContinuousOn U₁ O₁) (hU₂ : ContinuousOn U₂ O₂)
    (hae₁ : U₁ =ᵐ[μ.restrict O₁] W) (hae₂ : U₂ =ᵐ[μ.restrict O₂] W) :
    EqOn U₁ U₂ (O₁ ∩ O₂) ∧
      ∀ x ∈ O₁ ∩ O₂, U₁ =ᶠ[𝓝 x] U₂ ∧
        ∀ j : ℕ, iteratedFDeriv ℝ j U₁ x = iteratedFDeriv ℝ j U₂ x := by
  have hsub₁ : O₁ ∩ O₂ ⊆ O₁ := inter_subset_left
  have hsub₂ : O₁ ∩ O₂ ⊆ O₂ := inter_subset_right
  have ha₁ : U₁ =ᵐ[μ.restrict (O₁ ∩ O₂)] W :=
    ae_restrict_of_ae_restrict_of_subset hsub₁ hae₁
  have ha₂ : U₂ =ᵐ[μ.restrict (O₁ ∩ O₂)] W :=
    ae_restrict_of_ae_restrict_of_subset hsub₂ hae₂
  have hae : U₁ =ᵐ[μ.restrict (O₁ ∩ O₂)] U₂ := ha₁.trans ha₂.symm
  have heq := Measure.eqOn_open_of_ae_eq hae (hO₁.inter hO₂)
    (hU₁.mono hsub₁) (hU₂.mono hsub₂)
  refine ⟨heq, ?_⟩
  intro x hx
  have hgerm : U₁ =ᶠ[𝓝 x] U₂ := by
    filter_upwards [(hO₁.inter hO₂).mem_nhds hx] with y hy
    exact heq hy
  exact ⟨hgerm, fun j => (hgerm.iteratedFDeriv ℝ j).self_of_nhds⟩

#print axioms ae_eq_of_l2_limit_of_ae_pointwise_limit
#print axioms ae_eq_on_of_tendsto_Lp_of_ae_representatives
#print axioms ae_eq_of_l2_limit_of_pointwise_limit_on_open
#print axioms exists_same_c2_canonical_limit_of_locally_h4_cauchy
#print axioms contDiffOn_two_canonical_of_locally_h4_cauchy
#print axioms canonical_local_representatives_compatible

end Yamabe3.Analysis.UniformElliptic
