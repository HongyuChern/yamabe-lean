import GreenMass.QuantitativeInversion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Genuine inverted coordinate ends

This module constructs a native partial diffeomorphism with an exterior
Euclidean source from a genuine smooth coordinate parametrization whose
source contains a ball about zero. Its target is exactly the punctured
coordinate neighborhood, and its complement in the once-punctured compact
manifold is compact. Neither an end diffeomorphism nor compactness of that
complement is an input. Normal/radial coordinates, Green estimates, AF decay,
and positive mass are not proved or assumed here.
-/

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace GreenMass.InvertedEnd

abbrev E := EuclideanSpace ℝ (Fin 3)
open InversionDifferential QuantitativeInversion

def exterior (ρ : ℝ) : Set E := {y | ρ⁻¹ < ‖y‖}
def puncturedBall (ρ : ℝ) : Set E := {x | x ≠ 0 ∧ ‖x‖ < ρ}

theorem inversion_involution (x : E) (hx : x ≠ 0) :
    inversion (inversion x) = x := by
  change (‖inversion x‖ ^ 2)⁻¹ • inversion x = x
  rw [norm_inversion x hx, inv_pow, inv_inv]
  change ‖x‖ ^ 2 • ((‖x‖ ^ 2)⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)), one_smul]

theorem inversion_ne_zero (x : E) (hx : x ≠ 0) : inversion x ≠ 0 := by
  intro h
  have hn := norm_inversion x hx
  rw [h, norm_zero] at hn
  exact (inv_ne_zero (norm_ne_zero_iff.mpr hx)) hn.symm

theorem exterior_ne_zero {ρ : ℝ} (hρ : 0 < ρ) {y : E}
    (hy : y ∈ exterior ρ) : y ≠ 0 := by
  apply norm_ne_zero_iff.mp
  exact (lt_trans (inv_pos.mpr hρ) hy).ne'

theorem inversion_mem_puncturedBall {ρ : ℝ} (hρ : 0 < ρ) {y : E}
    (hy : y ∈ exterior ρ) : inversion y ∈ puncturedBall ρ := by
  have hyn := exterior_ne_zero hρ hy
  refine ⟨inversion_ne_zero y hyn, ?_⟩
  rw [norm_inversion y hyn]
  simpa only [inv_inv] using
    (inv_lt_inv₀ (norm_pos_iff.mpr hyn) (inv_pos.mpr hρ)).2 hy

theorem inversion_mem_exterior {ρ : ℝ} (hρ : 0 < ρ) {x : E}
    (hx : x ∈ puncturedBall ρ) : inversion x ∈ exterior ρ := by
  change ρ⁻¹ < ‖inversion x‖
  rw [norm_inversion x hx.1]
  exact (inv_lt_inv₀ hρ (norm_pos_iff.mpr hx.1)).2 hx.2

theorem contDiffAt_inversion {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ inversion x := by
  change ContDiffAt ℝ ∞ (fun z : E => (‖z‖ ^ 2)⁻¹ • z) x
  exact ((contDiff_norm_sq ℝ).contDiffAt.inv
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul contDiffAt_id

/-- Inversion is a genuine smooth partial diffeomorphism between the exterior
of radius `ρ⁻¹` and the punctured ball of radius `ρ`. -/
def inversionDiffeomorph (ρ : ℝ) (hρ : 0 < ρ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E E ∞ where
  toFun := inversion
  invFun := inversion
  source := exterior ρ
  target := puncturedBall ρ
  map_source' y hy := inversion_mem_puncturedBall hρ hy
  map_target' x hx := inversion_mem_exterior hρ hx
  left_inv' y hy := inversion_involution y (exterior_ne_zero hρ hy)
  right_inv' x hx := inversion_involution x hx.1
  open_source := isOpen_lt continuous_const continuous_norm
  open_target := isOpen_ne.inter
    (isOpen_lt continuous_norm continuous_const)
  contMDiffOn_toFun y hy :=
    (contMDiffAt_iff_contDiffAt.mpr
      (contDiffAt_inversion (exterior_ne_zero hρ hy))).contMDiffWithinAt
  contMDiffOn_invFun x hx :=
    (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_inversion hx.1)).contMDiffWithinAt

theorem puncturedBall_subset_ball (ρ : ℝ) : puncturedBall ρ ⊆ ball (0 : E) ρ := by
  intro x hx
  simpa only [mem_ball, dist_zero_right] using hx.2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- This is the actual composition of the coordinate parametrization with
the smooth inversion, with its genuine inverse and smooth structures. -/
def chartEnd (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞ :=
  (inversionDiffeomorph ρ hρ).trans e

theorem chartEnd_apply (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (y : E) :
    chartEnd e ρ hρ y = e (inversion y) := rfl

theorem chartEnd_source (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    (chartEnd e ρ hρ).source = exterior ρ := by
  ext y
  change (y ∈ exterior ρ ∧ inversion y ∈ e.source) ↔ y ∈ exterior ρ
  exact ⟨And.left, fun hy =>
    ⟨hy, hball (puncturedBall_subset_ball ρ (inversion_mem_puncturedBall hρ hy))⟩⟩

theorem chartEnd_target (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    (chartEnd e ρ hρ).target = (e '' ball (0 : E) ρ) \ {e 0} := by
  have hzero : (0 : E) ∈ e.source := hball (mem_ball_self hρ)
  have hsub : puncturedBall ρ ⊆ e.source :=
    (puncturedBall_subset_ball ρ).trans hball
  have ht : (chartEnd e ρ hρ).target = e '' puncturedBall ρ := by
    change ((inversionDiffeomorph ρ hρ).toPartialEquiv.trans
      e.toPartialEquiv).target = _
    rw [PartialEquiv.trans_target'']
    change e '' (e.source ∩ puncturedBall ρ) = _
    rw [inter_eq_right.mpr hsub]
  rw [ht]
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, puncturedBall_subset_ball ρ hx, rfl⟩, ?_⟩
    intro heq
    exact hx.1 (e.toPartialEquiv.injOn (hsub hx) hzero heq)
  · rintro ⟨⟨x, hx, rfl⟩, hne⟩
    refine ⟨x, ⟨?_, ?_⟩, rfl⟩
    · intro hx0
      apply hne
      change e x = e 0
      exact congrArg e hx0
    · simpa only [mem_ball, dist_zero_right] using hx

theorem coordinateBall_isOpen
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hball : ball (0 : E) ρ ⊆ e.source) :
    IsOpen (e '' ball (0 : E) ρ) :=
  e.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball hball

/-- A coordinate end omits a genuinely compact core of the punctured
manifold. The compactness is derived from compactness of the original
manifold, rather than being part of the end's data. -/
theorem chartEnd_complement_isCompact [CompactSpace M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    IsCompact {x : {q : M // q ≠ e 0} | x.val ∉ (chartEnd e ρ hρ).target} := by
  have hp : e 0 ∈ e '' ball (0 : E) ρ := ⟨0, mem_ball_self hρ, rfl⟩
  apply Subtype.isCompact_iff.mpr
  have heq : (Subtype.val ''
      {x : {q : M // q ≠ e 0} | x.val ∉ (chartEnd e ρ hρ).target}) =
      (e '' ball (0 : E) ρ)ᶜ := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      intro hmem
      apply hx
      rw [chartEnd_target e ρ hρ hball]
      exact ⟨hmem, x.property⟩
    · intro hq
      have hqp : q ≠ e 0 := by
        intro h
        exact hq (h.symm ▸ hp)
      refine ⟨⟨q, hqp⟩, ?_, rfl⟩
      rw [chartEnd_target e ρ hρ hball]
      exact fun h => hq h.1
  rw [heq]
  exact (coordinateBall_isOpen e ρ hball).isClosed_compl.isCompact

/-- Every exterior coordinate region in dimension three is path connected. -/
theorem exterior_isPathConnected {ρ : ℝ} (hρ : 0 < ρ) :
    IsPathConnected (exterior ρ) := by
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  let f : E × ℝ → E := fun z => z.2 • z.1
  have hcont : Continuous f := continuous_snd.smul continuous_fst
  have hprod : IsPathConnected (sphere (0 : E) 1 ×ˢ Ioi ρ⁻¹) :=
    (isPathConnected_sphere hrank 0 (by norm_num : (0 : ℝ) ≤ 1)).prod
      ((convex_Ioi ρ⁻¹).isPathConnected nonempty_Ioi)
  have himage := hprod.image' hcont.continuousOn
  have heq : f '' (sphere (0 : E) 1 ×ˢ Ioi ρ⁻¹) = exterior ρ := by
    ext y
    constructor
    · rintro ⟨⟨θ, t⟩, ⟨hθ, ht⟩, rfl⟩
      have hθn : ‖θ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hθ
      have htpos : 0 < t := (inv_pos.mpr hρ).trans ht
      change ρ⁻¹ < ‖t • θ‖
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hθn, mul_one, mem_Ioi] using ht
    · intro hy
      have hyn := exterior_ne_zero hρ hy
      have hn := norm_ne_zero_iff.mpr hyn
      refine ⟨(‖y‖⁻¹ • y, ‖y‖), ⟨?_, hy⟩, ?_⟩
      · change ‖‖y‖⁻¹ • y - 0‖ = 1
        rw [sub_zero, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hn]
      · change ‖y‖ • (‖y‖⁻¹ • y) = y
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rwa [heq] at himage

/-- The actual punctured coordinate neighborhood is path connected. -/
theorem chartEnd_target_isPathConnected
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (ρ : ℝ) (hρ : 0 < ρ) (hball : ball (0 : E) ρ ⊆ e.source) :
    IsPathConnected (chartEnd e ρ hρ).target := by
  have hs : IsPathConnected (chartEnd e ρ hρ).source := by
    rw [chartEnd_source e ρ hρ hball]
    exact exterior_isPathConnected hρ
  have hi := hs.image' (chartEnd e ρ hρ).contMDiffOn_toFun.continuousOn
  change IsPathConnected ((chartEnd e ρ hρ).toPartialEquiv ''
    (chartEnd e ρ hρ).source) at hi
  rwa [(chartEnd e ρ hρ).toPartialEquiv.image_source_eq_target] at hi

/-- Inverted coordinate ends are cofinal outside compact subsets of the
actual punctured space. Combined with the compact-core and connectedness
theorems, this supplies the topology of a single end; no end-count axiom or
properness field is assumed. -/
theorem chartEnd_cofinal [T2Space M]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞) (hzero : (0 : E) ∈ e.source)
    (K : Set {q : M // q ≠ e 0}) (hK : IsCompact K) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ball (0 : E) ρ ⊆ e.source ∧
      Disjoint (chartEnd e ρ hρ).target (Subtype.val '' K) := by
  let C : Set M := Subtype.val '' K
  have hC : IsCompact C := hK.image continuous_subtype_val
  have hp : e 0 ∉ C := by
    rintro ⟨x, _, hx⟩
    exact x.property hx
  have he : ContinuousAt e 0 :=
    e.contMDiffOn_toFun.continuousOn.continuousAt (e.open_source.mem_nhds hzero)
  have hn : e.source ∩ e ⁻¹' Cᶜ ∈ 𝓝 (0 : E) :=
    inter_mem (e.open_source.mem_nhds hzero)
      (he.preimage_mem_nhds (hC.isClosed.isOpen_compl.mem_nhds hp))
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp hn
  have hball : ball (0 : E) ρ ⊆ e.source := fun x hx => (hb hx).1
  refine ⟨ρ, hρ, hball, Set.disjoint_left.mpr ?_⟩
  intro q hq hqK
  rw [chartEnd_target e ρ hρ hball] at hq
  rcases hq.1 with ⟨x, hx, rfl⟩
  exact (hb hx).2 hqK

#print axioms inversion_involution
#print axioms inversionDiffeomorph
#print axioms chartEnd_source
#print axioms chartEnd_target
#print axioms chartEnd_complement_isCompact
#print axioms exterior_isPathConnected
#print axioms chartEnd_target_isPathConnected
#print axioms chartEnd_cofinal

end GreenMass.InvertedEnd
