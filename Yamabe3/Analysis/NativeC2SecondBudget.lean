import Yamabe3.Analysis.NativeInteriorSecondBound
import Yamabe3.Analysis.NativeCoordinateC2Weak

/-! The quantitative weak estimate controls the actual classical
Hessian of the same compact C² field. No Hessian bound is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Poincare.Analysis.Sobolev.Weak

def nativeCoordinateFirst (i : Fin 3) (u : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ u x (EuclideanSpace.single i 1)
def nativeCoordinateSecond (k i : Fin 3) (u : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ (nativeCoordinateFirst i u) x (EuclideanSpace.single k 1)

theorem nativeCoordinateFirst_congr_germ {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) (i : Fin 3) :
    nativeCoordinateFirst i u =ᶠ[𝓝 x] nativeCoordinateFirst i v := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hy

theorem nativeCoordinateSecond_congr_germ {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) (k i : Fin 3) : nativeCoordinateSecond k i u x = nativeCoordinateSecond k i v x :=
  congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single k 1))
    (nativeCoordinateFirst_congr_germ h i).fderiv_eq

theorem nativeCoordinateLaplacian_congr_germ {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) : nativeCoordinateLaplacian u x = nativeCoordinateLaplacian v x :=
  Finset.sum_congr rfl (fun i _ => nativeCoordinateSecond_congr_germ h i i)

theorem exists_uniform_C2_compact_second_budget
    {W V : Set E} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ (U : Set E) (C : Fin 3 → ℝ),IsOpen U ∧ IsCompact (closure U) ∧
      closure V ⊆ U ∧ closure U ⊆ W ∧ (∀ k,0 ≤ C k) ∧
      ∀ u : E → ℝ,ContDiff ℝ 2 u → HasCompactSupport u → ∀ k i : Fin 3,
        eLpNorm (nativeCoordinateSecond k i u) 2 (volume.restrict V) ≤
          ENNReal.ofReal (Real.sqrt (C k*((∫ x in U,∑ j,nativeCoordinateFirst j u x^2)+
            (∫ x in U,u x^2)+(∫ x in U,nativeCoordinateLaplacian u x^2)))) := by
  obtain ⟨U,C,hU,hUc,hVU,hUW,hC,hbound⟩ :=
    exists_uniform_interior_second_weak_bound (euclideanPrincipalForm univ) hW hV hVc hVW
  refine ⟨U,C,hU,hUc,hVU,hUW,hC,?_⟩
  intro u hu hc k i
  have hd := nativeCoordinateC2_compact_data hu hc
  have hflux (j : Fin 3) :
      (fun x => ∑ l,(euclideanPrincipalForm univ).a x l j*nativeCoordinateFirst l u x) =
        nativeCoordinateFirst j u := by
    funext x
    simp [euclideanPrincipalForm,Matrix.one_apply]
  have heq : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
      (∫ x in W,∑ j,(∑ l,(euclideanPrincipalForm univ).a x l j*nativeCoordinateFirst l u x)*
        fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in W,(-nativeCoordinateLaplacian u x)*φ x := by
    intro φ hφ hφc hs
    simp_rw [show ∀ x j,(∑ l,(euclideanPrincipalForm univ).a x l j*nativeCoordinateFirst l u x) =
      nativeCoordinateFirst j u x from fun x j => congrFun (hflux j) x]
    exact nativeCoordinateLaplacian_weakEquation hW hu φ hφ hφc hs
  obtain ⟨q,hq,hw,hqb⟩ := hbound u (fun x => -nativeCoordinateLaplacian u x)
    (fun j => nativeCoordinateFirst j u) hd.1 hd.2.2.1 hd.2.1 hd.2.2.2
    (fun j => by rw [hflux j]; exact hd.2.1 j) heq k i
  have hp : ContDiff ℝ 1 (nativeCoordinateFirst i u) :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hpc : HasCompactSupport (nativeCoordinateFirst i u) := hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsec : MemLp (nativeCoordinateSecond k i u) 2 (volume.restrict V) :=
    ((((hp.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hpc.fderiv_apply ℝ (EuclideanSpace.single k 1)))).restrict V
  have hweak := native_hasWeakPartialDeriv_of_contDiffOn_one hV hp.contDiffOn k
  have hae := HasWeakPartialDeriv.ae_eq hV hw hweak
    (hq.locallyIntegrable (by norm_num)) (hsec.locallyIntegrable (by norm_num))
  change q =ᵐ[volume.restrict V] nativeCoordinateSecond k i u at hae
  rw [← eLpNorm_congr_ae hae]
  simpa only [neg_sq] using hqb

#print axioms nativeCoordinateSecond_congr_germ
#print axioms exists_uniform_C2_compact_second_budget
end Yamabe3.Analysis.SpherePolar
