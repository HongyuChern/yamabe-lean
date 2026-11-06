import Yamabe3.Analysis.NativePoissonInfiniteH2Collar
import Yamabe3.Analysis.L2JointRepresentative
import Yamabe3.Analysis.Cylinder.NativeContinuousAngularFilterApproximation
import Yamabe3.Analysis.Cylinder.NativeAngularPhysicalH1

/-! The genuine Hilbert-valued entrance reflection. Its coefficients are
exactly the ones used for the physical collar; a joint representative is
constructed, not supplied as a new hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

def nativePoissonReflectedCurve (P : NativeHighPotential) (b : AngularH1) (t : ℝ) : AngularL2 :=
  if 0 ≤ t then P.curve b t else
    ∑ j : Fin 3,halfLineC2Coeffs j • P.curve b (-halfLineC2Rates j*t)

theorem nativePoissonReflectedCurve_continuous (P : NativeHighPotential) (b : AngularH1) :
    Continuous (nativePoissonReflectedCurve P b) := by
  have hU : Continuous (P.curve b) := by
    change Continuous (fun t : ℝ => Real.exp (-2*t) •
      nativeHalfHighPotentialPoissonCLM P.κ_nonneg P.κ_lt_one P.potential
        P.kernel_bound P.nonneg b t.toNNReal)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((nativeHalfHighPotentialPoissonCLM P.κ_nonneg P.κ_lt_one P.potential
        P.kernel_bound P.nonneg b).continuous.comp (by fun_prop))
  unfold nativePoissonReflectedCurve
  apply continuous_if
  · intro t ht
    have ht0 : t=0 := by
      change t ∈ frontier (Ici (0:ℝ)) at ht
      simpa only [frontier_Ici,mem_singleton_iff] using ht
    subst t
    simp only [mul_zero,← Finset.sum_smul]
    have hc : ∑ j : Fin 3,halfLineC2Coeffs j=(1:ℝ) := by
      norm_num [halfLineC2Coeffs,Fin.sum_univ_succ]
    rw [hc,one_smul]
  · exact hU.continuousOn
  · apply Continuous.continuousOn
    apply continuous_finsetSum
    intro j _
    exact (continuous_const : Continuous (fun _ : ℝ => halfLineC2Coeffs j)).smul
      (hU.comp (continuous_const.mul continuous_id))

theorem nativePoissonReflectedCurve_coefficient (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) (t : ℝ) :
    inner ℝ (angularBasis i) (nativePoissonReflectedCurve P b t) = nativePoissonEntranceExtension P b i t := by
  unfold nativePoissonReflectedCurve nativePoissonEntranceExtension halfLineC2Extension halfLineReflection
  split_ifs <;> simp only [nativePoissonCoordinate,inner_sum,real_inner_smul_right]

theorem nativePoissonReflectedCurve_finite_lift (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    cylinderLift (projectedAngular s (nativePoissonReflectedCurve P b)) = nativePoissonFiniteCollar P b s := by
  unfold projectedAngular
  simp_rw [nativePoissonReflectedCurve_coefficient]
  exact (finitePhysical_eq_lift s _).symm

theorem nativePoissonReflectedCurve_joint_representative (P : NativeHighPotential) (b : AngularH1) :
    ∃ w : ℝ × S → ℝ,StronglyMeasurable w ∧
      (∀ t,(fun θ => w (t,θ)) =ᵐ[angularVolume] (nativePoissonReflectedCurve P b t : S → ℝ)) ∧
      (∀ t,0 ≤ t → (fun θ => w (t,θ)) =ᵐ[angularVolume] (P.curve b t : S → ℝ)) := by
  obtain ⟨w,hw,hae⟩ := exists_joint_L2_representative_of_continuous (nativePoissonReflectedCurve_continuous P b)
  have hae' (t : ℝ) : (fun θ => w (t,θ)) =ᵐ[angularVolume] (nativePoissonReflectedCurve P b t : S → ℝ) := by
    simpa only [Measure.restrict_univ] using hae t
  refine ⟨w,hw,hae',fun t ht => ?_⟩
  simpa only [nativePoissonReflectedCurve,if_pos ht] using hae' t

#print axioms nativePoissonReflectedCurve_coefficient
#print axioms nativePoissonReflectedCurve_joint_representative
end Yamabe3.Analysis.SpherePolar
