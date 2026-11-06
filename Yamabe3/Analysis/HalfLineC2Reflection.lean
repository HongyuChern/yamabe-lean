import Yamabe3.Analysis.HalfLineFiniteReflection

/-! Three genuine positive-time samples extend a half-line C² field.
The three moment identities preserve its entrance value and both jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

def halfLineC2Rates : Fin 3 → ℝ := ![1,2,3]
def halfLineC2Coeffs : Fin 3 → ℝ := ![6,-8,3]
def halfLineC2Extension (f : ℝ → ℝ) : ℝ → ℝ :=
  halfLineReflection halfLineC2Rates halfLineC2Coeffs f

theorem halfLineC2Extension_contDiff
    {f df ddf : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (df t) (Ici 0) t)
    (hdf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt df (ddf t) (Ici 0) t)
    (hddf : ContinuousOn ddf (Ici 0)) :
    ContDiff ℝ 2 (halfLineC2Extension f) := by
  let r := halfLineC2Rates
  let c := halfLineC2Coeffs
  let c1 := fun j => -r j*c j
  let c2 := fun j => -r j*c1 j
  have hr : ∀ j, 0 < r j := by intro j; fin_cases j <;> norm_num [r,halfLineC2Rates]
  have hc : ∑ j,c j = 1 := by norm_num [c,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hc1 : ∑ j,c1 j = 1 := by norm_num [c1,c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hc2 : ∑ j,c2 j = 1 := by norm_num [c2,c1,c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hD := halfLineReflection_hasDeriv r c hr hc hc1 hf
  have hDD := halfLineReflection_hasDeriv r c1 hr hc1 hc2 hdf
  have heD : deriv (halfLineC2Extension f) = halfLineReflection r c1 df :=
    funext fun t => (hD t).deriv
  have heDD : deriv (halfLineReflection r c1 df) = halfLineReflection r c2 ddf :=
    funext fun t => (hDD t).deriv
  rw [show (2:ℕ∞ω) = 1+1 from rfl,contDiff_succ_iff_deriv]
  refine ⟨fun t => (hD t).differentiableAt,by simp,?_⟩
  rw [heD,contDiff_one_iff_deriv]
  refine ⟨fun t => (hDD t).differentiableAt,?_⟩
  rw [heDD]
  exact halfLineReflection_continuous r c2 hr hc2 hddf

theorem halfLineC2Extension_jets
    {f df ddf : ℝ → ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (df t) (Ici 0) t)
    (hdf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt df (ddf t) (Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) :
    halfLineC2Extension f t = f t ∧
    deriv (halfLineC2Extension f) t = df t ∧
    deriv (deriv (halfLineC2Extension f)) t = ddf t := by
  let r := halfLineC2Rates
  let c := halfLineC2Coeffs
  let c1 := fun j => -r j*c j
  let c2 := fun j => -r j*c1 j
  have hr : ∀ j, 0 < r j := by intro j; fin_cases j <;> norm_num [r,halfLineC2Rates]
  have hc : ∑ j,c j = 1 := by norm_num [c,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hc1 : ∑ j,c1 j = 1 := by norm_num [c1,c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hc2 : ∑ j,c2 j = 1 := by norm_num [c2,c1,c,r,halfLineC2Rates,halfLineC2Coeffs,Fin.sum_univ_succ]
  have hD := halfLineReflection_hasDeriv r c hr hc hc1 hf
  have hDD := halfLineReflection_hasDeriv r c1 hr hc1 hc2 hdf
  have heD : deriv (halfLineC2Extension f) = halfLineReflection r c1 df :=
    funext fun s => (hD s).deriv
  refine ⟨halfLineReflection_eq_nonneg r c f ht,?_,?_⟩
  · rw [heD,halfLineReflection_eq_nonneg r c1 df ht]
  · rw [heD,(hDD t).deriv,halfLineReflection_eq_nonneg r c2 ddf ht]

#print axioms halfLineC2Extension_contDiff
#print axioms halfLineC2Extension_jets
end Yamabe3.Analysis.Delaunay
