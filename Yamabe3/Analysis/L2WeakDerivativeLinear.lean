import Yamabe3.Analysis.L2WeakSeries

/-! The actual weak derivative of a linear L2 value family is itself
linear by uniqueness. The graph of the same weak derivative is closed
in the genuine L2 product, enabling bounded source extension. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem native_weakPartial_Lp_add {Ω : Set E} {i : Fin d}
    {f₁ f₂ g₁ g₂ : Lp ℝ 2 (volume.restrict Ω)}
    (h₁ : HasWeakPartialDeriv i g₁ f₁ Ω) (h₂ : HasWeakPartialDeriv i g₂ f₂ Ω) :
    HasWeakPartialDeriv i ⇑(g₁+g₂) ⇑(f₁+f₂) Ω := by
  have hh : ∀ a : Fin 2,HasWeakPartialDeriv i (![g₁,g₂] a) (![f₁,f₂] a) Ω := by
    intro a
    fin_cases a
    · exact h₁
    · exact h₂
  have h := native_weakPartial_Lp_finset_sum hh Finset.univ
  simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_succ,
    add_zero] using h

theorem native_weakPartial_Lp_smul {Ω : Set E} {i : Fin d}
    {f g : Lp ℝ 2 (volume.restrict Ω)} (c : ℝ) (h : HasWeakPartialDeriv i g f Ω) :
    HasWeakPartialDeriv i ⇑(c • g) ⇑(c • f) Ω := by
  apply native_weakPartial_transfer_ae (Lp.coeFn_smul c f) (Lp.coeFn_smul c g)
  intro φ hφ hc hs
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul,h φ hφ hc hs]
  ring

def nativeL2WeakDerivativeLinearMap {X : Type*} [AddCommGroup X] [Module ℝ X]
    {Ω : Set E} (hΩ : IsOpen Ω) (i : Fin d)
    (f : X →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω)) (g : X → Lp ℝ 2 (volume.restrict Ω))
    (hw : ∀ x,HasWeakPartialDeriv i (g x) (f x) Ω) : X →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) where
  toFun := g
  map_add' x y := by
    apply Lp.ext
    have hx : HasWeakPartialDeriv i (g (x+y)) ⇑(f x+f y) Ω := by simpa only [map_add] using hw (x+y)
    exact hx.ae_eq hΩ (native_weakPartial_Lp_add (hw x) (hw y))
      ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))
  map_smul' c x := by
    apply Lp.ext
    have hx : HasWeakPartialDeriv i (g (c • x)) ⇑(c • f x) Ω := by simpa only [map_smul] using hw (c • x)
    exact hx.ae_eq hΩ (native_weakPartial_Lp_smul c (hw x))
      ((Lp.memLp _).locallyIntegrable (by norm_num)) ((Lp.memLp _).locallyIntegrable (by norm_num))

theorem native_weakPartial_Lp_graph_closed {Ω : Set E} (i : Fin d) :
    IsClosed {z : Lp ℝ 2 (volume.restrict Ω) × Lp ℝ 2 (volume.restrict Ω) |
      HasWeakPartialDeriv i z.2 z.1 Ω} := by
  apply isSeqClosed_iff_isClosed.mp
  intro z Z hz hZ
  exact native_weak_partial_of_tendsto_L2_filter i
    (continuous_fst.continuousAt.tendsto.comp hZ)
    (continuous_snd.continuousAt.tendsto.comp hZ) hz

#print axioms native_weakPartial_Lp_add
#print axioms native_weakPartial_Lp_smul
#print axioms nativeL2WeakDerivativeLinearMap
#print axioms native_weakPartial_Lp_graph_closed
end Yamabe3.Analysis.UniformElliptic
