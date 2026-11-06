import Yamabe3.Analysis.NativeInteriorQuantitative
import PoincareLib.Analysis.Elliptic.Regularity.SecondDerivative
import PoincareLib.Analysis.Sobolev.Euclidean.L2

/-! Actual second weak derivatives with an explicit uniform budget.
The sets and all constants are chosen before the field and source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev
open Weak NirenbergEuclidean NirenbergCrossBoundsNonSmooth NirenbergAssembly
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_uniform_interior_second_weak_bound
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ (U : Set E) (C : Fin d → ℝ),IsOpen U ∧ IsCompact (closure U) ∧
      closure V ⊆ U ∧ closure U ⊆ W ∧ (∀ k,0 ≤ C k) ∧
      ∀ (u f : E → ℝ) (p : Fin d → E → ℝ),
      MemLp u 2 volume → MemLp f 2 volume → (∀ i,MemLp (p i) 2 volume) →
      (∀ i,HasWeakPartialDeriv i (p i) u univ) →
      (∀ j,MemLp (fun x => ∑ i,B.a x i j*p i x) 2 volume) →
      (∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
        (∫ x in W,∑ j,(∑ i,B.a x i j*p i x)*fderiv ℝ φ x (EuclideanSpace.single j 1)) =
          ∫ x in W,f x*φ x) →
      ∀ k i : Fin d,∃ q : E → ℝ,MemLp q 2 (volume.restrict V) ∧
        HasWeakPartialDeriv k q (p i) V ∧ eLpNorm q 2 (volume.restrict V) ≤
          ENNReal.ofReal (Real.sqrt (C k*((∫ x in U,∑ j,p j x^2)+
            (∫ x in U,u x^2)+(∫ x in U,f x^2)))) := by
  classical
  obtain ⟨U₀,hU₀,hVU₀,hU₀c⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  obtain ⟨U,hU,hVU,hUW₀⟩ := hVc.exists_isOpen_closure_subset
    ((hW.inter hU₀).mem_nhdsSet.mpr (subset_inter hVW hVU₀))
  have hUc : IsCompact (closure U) := hU₀c.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure ((hUW₀ hx).2))
  have hUW : closure U ⊆ W := fun x hx => (hUW₀ hx).1
  obtain ⟨η,hη,hηc,hηrange,hηone,hηU,N,hN,hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hVc hU hVU
  obtain ⟨R,hR,hRU⟩ := hηc.isCompact.exists_cthickening_subset_open hU hηU
  let C : Fin d → ℝ := fun k => nirenbergMasterYoungConstant B N hUc k/(B.lam/2)
  refine ⟨U,C,hU,hUc,hVU,hUW,?_,?_⟩
  · intro k
    exact div_nonneg (nirenbergMasterYoungConstant_nonneg B hN hUc k)
      (div_pos B.hlam_pos (by norm_num)).le
  intro u f p hu hf hp hw hF heq k i
  let C₀ := C k*((∫ x in U,∑ j,p j x^2)+(∫ x in U,u x^2)+(∫ x in U,f x^2))
  have hC (h : ℝ) (hh : h ≠ 0) (hle : |h| ≤ R) := native_diffQuot_weakGradient_quantitative B hW hu hf hp hw hF heq
    hη hηc hηrange hN hDη hU (subset_univ _) hUc (subset_closure.trans hUW) hR
    (fun {h} hh => (Metric.cthickening_mono hh _).trans hRU)
    (fun x hx => hηone x (subset_closure hx)) hV.measurableSet k (h := h) hh hle
  have hbound (h : ℝ) (hh : 0 < |h|) (hle : |h| ≤ R) :
      eLpNorm (diffQuot k h (p i)) 2 (volume.restrict V) ≤ ENNReal.ofReal (Real.sqrt C₀) := by
    have hq (j : Fin d) := (memLp_diffQuot_two k h (hp j)).restrict V
    have hsq (j : Fin d) := (hq j).integrable_sq
    apply eLpNorm_two_le_sqrt_of_integral_sq_le (hq i)
    calc
      _ ≤ ∫ x in V,∑ j : Fin d,diffQuot k h (p j) x^2 := by
        apply integral_mono (hsq i) (integrable_finsetSum _ (fun j _ => hsq j))
        intro x
        exact Finset.single_le_sum (fun j _ => sq_nonneg (diffQuot k h (p j) x)) (Finset.mem_univ i)
      _ ≤ C₀ := by
        have hd : (0:ℝ) < B.lam/2 := div_pos B.hlam_pos (by norm_num)
        have hhC : (∫ x in V,∑ j : Fin d,diffQuot k h (p j) x^2) ≤
            (nirenbergMasterYoungConstant B N hUc k *
              ((∫ x in U,∑ j,p j x^2)+(∫ x in U,u x^2)+(∫ x in U,f x^2)))/(B.lam/2) := by
          apply (le_div_iff₀ hd).mpr
          simpa only [mul_comm] using hC h (abs_pos.mp hh) hle
        convert hhC using 1 <;> dsimp only [C₀,C] <;> ring

  obtain ⟨q,hq,hweak,hnorm⟩ := hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc
    isOpen_univ hV hVc hR (subset_univ _) (by simpa using hp i)
    k (Real.sqrt_nonneg C₀) hbound
  exact ⟨q,hq,hweak,hnorm⟩

#print axioms exists_uniform_interior_second_weak_bound
end Yamabe3.Analysis.UniformElliptic
