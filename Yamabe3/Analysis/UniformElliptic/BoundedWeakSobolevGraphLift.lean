import Yamabe3.Analysis.UniformElliptic.WeakSobolevGraphSpace

/-! A bounded graph lift from proved Sobolev regularity of one fixed
linear value map. Linearity follows from uniqueness of actual weak jets,
not from a fresh choice of derivatives for each algebraic operation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean
local notation "E3" => EuclideanSpace ℝ (Fin 3)
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def boundedWeakSobolevGraphLift
    (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ f i, MemWkp k 2 (P f i) V)
    (hb : ∀ f i, (iteratedWeakSobolevNorm k 2 (P f i) V).toReal ≤ C * ‖f‖) :
    X →L[ℝ] weakSobolevGraph V hV k P := by
  let Q : X →ₗ[ℝ] weakSobolevGraph V hV k P :=
    { toFun := fun f => weakSobolevGraphOfBound V hV k P f (hu f) (C * ‖f‖) (hb f)
      map_add' := fun f g => weakSobolevGraph_fst_injective V hV k P rfl
      map_smul' := fun c f => weakSobolevGraph_fst_injective V hV k P rfl }
  apply Q.mkContinuous (max 1 C)
  intro f
  exact (weakSobolevGraphOfBound_norm_le V hV k P f (hu f) (C * ‖f‖)
    (mul_nonneg hC (norm_nonneg f)) (hb f)).trans (by
      rw [max_mul_of_nonneg _ _ (norm_nonneg f), one_mul])

@[simp] theorem boundedWeakSobolevGraphLift_value
    (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ f i, MemWkp k 2 (P f i) V)
    (hb : ∀ f i, (iteratedWeakSobolevNorm k 2 (P f i) V).toReal ≤ C * ‖f‖) (f : X) :
    weakSobolevGraphValue V hV k P (boundedWeakSobolevGraphLift V hV k P C hC hu hb f) = f := rfl

theorem boundedWeakSobolevGraphLift_norm_le
    (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ f i, MemWkp k 2 (P f i) V)
    (hb : ∀ f i, (iteratedWeakSobolevNorm k 2 (P f i) V).toReal ≤ C * ‖f‖) :
    ‖boundedWeakSobolevGraphLift V hV k P C hC hu hb‖ ≤ max 1 C := by
  apply LinearMap.mkContinuous_norm_le _ (le_max_of_le_left (by norm_num))
  intro f
  exact (weakSobolevGraphOfBound_norm_le V hV k P f (hu f) (C * ‖f‖)
    (mul_nonneg hC (norm_nonneg f)) (hb f)).trans (by
      rw [max_mul_of_nonneg _ _ (norm_nonneg f), one_mul])

#print axioms boundedWeakSobolevGraphLift
#print axioms boundedWeakSobolevGraphLift_value
#print axioms boundedWeakSobolevGraphLift_norm_le
end Yamabe3.Analysis.UniformElliptic
