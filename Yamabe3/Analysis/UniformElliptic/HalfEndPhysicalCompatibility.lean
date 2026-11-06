import Yamabe3.Analysis.UniformElliptic.NativeDelaunayHalfEndOperator

/-!
# Compatibility and completion of the same physical half-end correction

The logarithmic slices are exact rescalings of one physical function. Their
pointwise limits retain that transition law on every actual overlap. A single
physical representative is constructed on the union of the annuli from these
limits; the original physical sequence converges to that representative there.
This file does not assert completeness of a Sobolev space or a linear inverse.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT Delaunay
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Returning a normalized slice to its physical scale recovers the same w. -/
theorem halfEndCoordinateCorrection_recover (ε : ℝ) (w : E3 → ℝ) (s : ℝ) (z : E3) :
    radialScale (ε * Real.exp (-s)) * halfEndCoordinateCorrection ε w s z =
      w ((ε * Real.exp (-s)) • z) := by
  unfold halfEndCoordinateCorrection
  rw [← mul_assoc, mul_inv_cancel₀ (radialScale_pos _).ne', one_mul]

/-- The exact transition law, including its conformal amplitude. Neither
parameter is restricted to a whole-line Banach topology. -/
theorem halfEndCoordinateCorrection_shift {ε : ℝ} (hε : 0 < ε)
    (w : E3 → ℝ) (s d : ℝ) (z : E3) :
    halfEndCoordinateCorrection ε w (s + d) z =
      Real.exp (-d / 2) * halfEndCoordinateCorrection ε w s (Real.exp (-d) • z) := by
  have hr : ε * Real.exp (-(s + d)) = (ε * Real.exp (-s)) * Real.exp (-d) := by
    rw [neg_add, Real.exp_add, mul_assoc]
  have ha : (radialScale (Real.exp (-d)))⁻¹ = Real.exp (-d / 2) := by
    unfold radialScale
    rw [Real.log_exp, ← Real.exp_neg]
    congr 1
    ring
  unfold halfEndCoordinateCorrection
  rw [hr, radialScale_mul_positive (mul_pos hε (Real.exp_pos _)) (Real.exp_pos _),
    mul_inv_rev, ha, mul_smul]
  ring

/-- On the entrance slice, the normalized correction is exactly the same
physical w at radius epsilon. -/
theorem halfEndCoordinateCorrection_zero (ε : ℝ) (w : E3 → ℝ) (z : E3) :
    halfEndCoordinateCorrection ε w 0 z = (radialScale ε)⁻¹ * w (ε • z) := by
  simp only [halfEndCoordinateCorrection, neg_zero, Real.exp_zero, mul_one]

/-- Pointwise limits of the same normalized physical sequence retain the
transition law wherever both slice evaluations belong to the chosen domain. -/
theorem halfEnd_limit_shift {ε : ℝ} (hε : 0 < ε) {Ω : Set E3}
    {w : ℕ → E3 → ℝ} {W : ℝ → E3 → ℝ}
    (hW : ∀ s, 0 ≤ s → ∀ z ∈ Ω,
      Tendsto (fun j => halfEndCoordinateCorrection ε (w j) s z) atTop (𝓝 (W s z)))
    {s d : ℝ} (hs : 0 ≤ s) (hsd : 0 ≤ s + d) {z : E3}
    (hz : z ∈ Ω) (hzd : Real.exp (-d) • z ∈ Ω) :
    W (s + d) z = Real.exp (-d / 2) * W s (Real.exp (-d) • z) := by
  apply tendsto_nhds_unique (hW (s + d) hsd z hz)
  simpa only [halfEndCoordinateCorrection_shift hε] using
    (hW s hs (Real.exp (-d) • z) hzd).const_mul (Real.exp (-d / 2))

/-- The actual physical region covered by the nonnegative logarithmic slices. -/
def halfEndAnnularRegion (ε : ℝ) (Ω : Set E3) : Set E3 :=
  {x | ∃ s : ℝ, 0 ≤ s ∧ ∃ z ∈ Ω, x = (ε * Real.exp (-s)) • z}

/-- A common physical sequence with convergent normalized slices has one
physical pointwise limit on the covered end. All supplied limiting slices
are precisely the normalizations of that same representative. In particular
no unrelated locally estimated solution is substituted during gluing. -/
theorem exists_same_physical_limit_of_halfEnd_pointwise
    (ε : ℝ) (Ω : Set E3) (w : ℕ → E3 → ℝ) (W : ℝ → E3 → ℝ)
    (hW : ∀ s, 0 ≤ s → ∀ z ∈ Ω,
      Tendsto (fun j => halfEndCoordinateCorrection ε (w j) s z) atTop (𝓝 (W s z))) :
    ∃ u : E3 → ℝ,
      (∀ x ∈ halfEndAnnularRegion ε Ω, Tendsto (fun j => w j x) atTop (𝓝 (u x))) ∧
      (∀ s, 0 ≤ s → ∀ z ∈ Ω, halfEndCoordinateCorrection ε u s z = W s z) := by
  classical
  have hex : ∀ x : E3, ∃ a : ℝ, x ∈ halfEndAnnularRegion ε Ω →
      Tendsto (fun j => w j x) atTop (𝓝 a) := by
    intro x
    by_cases hx : x ∈ halfEndAnnularRegion ε Ω
    · obtain ⟨s, hs, z, hz, hzx⟩ := hx
      refine ⟨radialScale (ε * Real.exp (-s)) * W s z, ?_⟩
      intro _
      have ht := (hW s hs z hz).const_mul (radialScale (ε * Real.exp (-s)))
      simpa only [halfEndCoordinateCorrection_recover, ← hzx] using ht
    · exact ⟨0, fun hx' => False.elim (hx hx')⟩
  choose u hu using hex
  refine ⟨u, hu, ?_⟩
  intro s hs z hz
  have hx : (ε * Real.exp (-s)) • z ∈ halfEndAnnularRegion ε Ω :=
    ⟨s, hs, z, hz, rfl⟩
  have ht := (hu ((ε * Real.exp (-s)) • z) hx).const_mul
    ((radialScale (ε * Real.exp (-s)))⁻¹)
  exact tendsto_nhds_unique ht (hW s hs z hz)

/-- The physical limit above is unique on the actual union of annuli. -/
theorem same_physical_limit_unique {ε : ℝ} {Ω : Set E3}
    {w : ℕ → E3 → ℝ} {u v : E3 → ℝ}
    (hu : ∀ x ∈ halfEndAnnularRegion ε Ω,
      Tendsto (fun j => w j x) atTop (𝓝 (u x)))
    (hv : ∀ x ∈ halfEndAnnularRegion ε Ω,
      Tendsto (fun j => w j x) atTop (𝓝 (v x))) :
    EqOn u v (halfEndAnnularRegion ε Ω) := by
  intro x hx
  exact tendsto_nhds_unique (hu x hx) (hv x hx)

#print axioms halfEndCoordinateCorrection_recover
#print axioms halfEndCoordinateCorrection_shift
#print axioms halfEnd_limit_shift
#print axioms exists_same_physical_limit_of_halfEnd_pointwise
#print axioms same_physical_limit_unique

end Yamabe3.Analysis.UniformElliptic
