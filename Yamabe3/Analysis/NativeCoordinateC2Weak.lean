import Yamabe3.Analysis.NativeFinitePolarLaplacian
import Yamabe3.Analysis.UniformElliptic.NativeC1Caccioppoli
import Yamabe3.Analysis.Cylinder.EuclideanJacobiEnergy

/-! The actual coordinate Laplacian of a C² field gives its weak
source, with all L² data available after compact localization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak

theorem nativeCoordinateLaplacian_weakEquation {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O,∑ i : Fin 3,fderiv ℝ u x (EuclideanSpace.single i 1)*
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O,(-nativeCoordinateLaplacian u x)*φ x := by
  let p := fun i : Fin 3 => fun x => fderiv ℝ u x (EuclideanSpace.single i 1)
  have hp (i : Fin 3) : ContDiff ℝ 1 (p i) :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hL (i : Fin 3) : IntegrableOn
      (fun x => p i x*fderiv ℝ φ x (EuclideanSpace.single i 1)) O :=
    (((hp i).continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left)).integrableOn
  have hR (i : Fin 3) : IntegrableOn
      (fun x => fderiv ℝ (p i) x (EuclideanSpace.single i 1)*φ x) O :=
    (((((hp i).continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hφ.continuous).integrable_of_hasCompactSupport
      hc.mul_left).integrableOn
  have hi (i : Fin 3) := native_hasWeakPartialDeriv_of_contDiffOn_one hO (hp i).contDiffOn i φ hφ hc hs
  change (∫ x in O,∑ i : Fin 3,p i x*fderiv ℝ φ x (EuclideanSpace.single i 1)) = _
  rw [integral_finsetSum _ (fun i _ => hL i)]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib]
  change -(∑ i : Fin 3,∫ x in O,fderiv ℝ (p i) x (EuclideanSpace.single i 1)*φ x) = _
  simp only [nativeCoordinateLaplacian,neg_mul,Finset.sum_mul,integral_neg,
    integral_finsetSum _ (fun i _ => hR i),p]

theorem nativeCoordinateC2_compact_data {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (hc : HasCompactSupport u) :
    MemLp u 2 volume ∧
    (∀ i : Fin 3,MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) 2 volume) ∧
    MemLp (fun x => -nativeCoordinateLaplacian u x) 2 volume ∧
    (∀ i : Fin 3,HasWeakPartialDeriv i
      (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) u univ) := by
  let p := fun i : Fin 3 => fun x => fderiv ℝ u x (EuclideanSpace.single i 1)
  have hp (i : Fin 3) : ContDiff ℝ 1 (p i) :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hpc (i : Fin 3) : HasCompactSupport (p i) := hc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  refine ⟨hu.continuous.memLp_of_hasCompactSupport hc,
    fun i => (hp i).continuous.memLp_of_hasCompactSupport (hpc i),?_,
    fun i => native_hasWeakPartialDeriv_of_contDiffOn_one isOpen_univ
      (hu.of_le (by norm_num)).contDiffOn i⟩
  apply MemLp.neg
  apply memLp_finsetSum
  intro i _
  exact (((hp i).continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
    ((hpc i).fderiv_apply ℝ (EuclideanSpace.single i 1))

#print axioms nativeCoordinateLaplacian_weakEquation
#print axioms nativeCoordinateC2_compact_data
end Yamabe3.Analysis.SpherePolar
