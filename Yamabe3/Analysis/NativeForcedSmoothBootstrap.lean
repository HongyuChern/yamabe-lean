import Yamabe3.Analysis.UniformElliptic.InhomogeneousBootstrap

/-!
# Local coefficients and an actual smooth source

The already proved inhomogeneous bootstrap is localized with the pinned
positive coefficient extension and then glued by almost-everywhere equality.
This is the Euclidean input for the native forced equation. Neither classical
regularity nor an elliptic inverse is an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic
open Poincare.Analysis.Sobolev.Weak

theorem exists_smooth_representative_of_compact_local_smooth_source
    {n : ℕ} (hn : 0 < n)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (Q F u : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (hQ : ContDiffOn ℝ ∞ Q O) (hF : ContDiffOn ℝ ∞ F O)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (heq : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, (F x + Q x * u x) * φ x) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ U O ∧ U =ᵐ[volume.restrict O] u := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  apply Poincare.Analysis.Elliptic.exists_smooth_representative_of_local
  intro x hx
  obtain ⟨V, hV, hxV, hVc, hVO, B, hBA, -⟩ :=
    exists_global_elliptic_extension hO (isCompact_singleton (x := x))
      (singleton_subset_iff.mpr hx) A Q hA hpos hQ
  have hVO' : V ⊆ O := subset_closure.trans hVO
  have huV := (hu (closure V) hVc hVO).mono_measure
    (Measure.restrict_mono subset_closure le_rfl)
  have hpV (i : Fin n) := (hp i (closure V) hVc hVO).mono_measure
    (Measure.restrict_mono subset_closure le_rfl)
  have hpartialV (i : Fin n) := (hpartial i).restrict hV hVO'
  have hposV : ∀ y ∈ V, (B.a y).PosDef := by
    intro y hy
    rw [hBA hy]
    exact hpos y (hVO' hy)
  have heqV : Iteration.WeakEquation V (Iteration.matrixFlux B.a p)
      (fun y => F y + Q y * u y) :=
    weakEquation_congr_restrict hVO' hBA (fun _ _ _ => rfl) heq
  obtain ⟨U, hUs, hUae⟩ := exists_smooth_representative_of_local_smooth_source
    hn hO hV hVc hVO B.smooth_a hposV hQ hF huV hpV hpartialV heqV
  exact ⟨V, hV, hxV (mem_singleton x), hVO', U, hUs, hUae⟩

#print axioms exists_smooth_representative_of_compact_local_smooth_source

end Yamabe3.Analysis.UniformElliptic
