import Yamabe3.Analysis.BanachFuturePotentialInverse

/-!
# True scalar equations of continuous linear observables

Both derivatives are obtained from the strong Banach derivatives by the
chain rule. This is used for actual native eigenbasis evaluation after the
aggregate low-angular inverse has already been constructed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem banachFuturePotentialInverse_observable_equation {k : ℝ} (hk : 0 < k)
    (A : ℝ →ᵇ (H →L[ℝ] H)) (hA : ‖A‖ < k ^ 2) (F : ℝ →ᵇ H)
    (L : H →L[ℝ] ℝ) (a : ℝ → ℝ)
    (hAL : ∀ t x, L (A t x) = a t * L x) :
    let y := fun t => L (banachFuturePotentialInverse k hk A hA F t)
    Differentiable ℝ y ∧ Differentiable ℝ (deriv y) ∧
      ∀ t, deriv (deriv y) t =
        2 * k * deriv y t - k ^ 2 * y t + L (F t) + a t * y t := by
  dsimp only
  let u := fun t => banachFuturePotentialInverse k hk A hA F t
  have h := banachFuturePotentialInverse_equation hk A hA F
  dsimp only at h
  have hd (t : ℝ) : HasDerivAt (fun s => L (u s)) (L (deriv u t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (h.1 t).hasDerivAt
  have he : deriv (fun s => L (u s)) = fun t => L (deriv u t) :=
    funext fun t => (hd t).deriv
  have hd2 (t : ℝ) : HasDerivAt (fun s => L (deriv u s)) (L (deriv (deriv u) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t (h.2.1 t).hasDerivAt
  refine ⟨fun t => (hd t).differentiableAt, ?_, fun t => ?_⟩
  · rw [he]
    exact fun t => (hd2 t).differentiableAt
  · change deriv (deriv (fun s => L (u s))) t = _
    rw [he, (hd2 t).deriv, h.2.2 t]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hAL]
    rfl

end Yamabe3.Analysis.Delaunay
