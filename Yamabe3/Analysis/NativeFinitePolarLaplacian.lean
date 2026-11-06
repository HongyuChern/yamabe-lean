import Yamabe3.Analysis.BubbleFinitePhysicalEquation
import Yamabe3.Analysis.Cylinder.NativeFiniteAngularEnergy
import Yamabe3.Analysis.Cylinder.NativeCylinderPullback

/-! Actual Euclidean Laplacian and actual induced-sphere square
integrals of finite C² fields, at every positive radius. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeCoordinateLaplacian (u : E → ℝ) (x : E) : ℝ :=
  ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x
    (EuclideanSpace.single j 1)

def finiteTimeLaplacian (q : AngularIndex → ℝ → ℝ) (i : AngularIndex) (t : ℝ) : ℝ :=
  deriv (deriv (q i)) t-(angularEigenvalue i+1/4)*q i t

theorem continuousOn_nativeCoordinateLaplacian {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u O) : ContinuousOn (nativeCoordinateLaplacian u) O := by
  apply continuousOn_finsetSum
  intro j _
  have hj : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) O :=
    (hu.fderiv_of_isOpen hO (by norm_num)).clm_apply contDiffOn_const
  exact (hj.continuousOn_fderiv_of_isOpen hO (by norm_num)).clm_apply continuousOn_const

theorem native_finitePhysical_laplacian (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (hq : ∀ i ∈ s, ContDiff ℝ 2 (q i))
    {x : E} (hx : x ≠ 0) :
    nativeCoordinateLaplacian (finitePhysical s q) x =
      cylinderLift (finiteAngular s (finiteTimeLaplacian q)) x / ‖x‖^2 := by
  have h := native_finitePhysical_negative_trace_eq_global_C2 (fun _ => 0) s q
    (finiteTimeLaplacian q) hq (fun i hi t => by dsimp only [finiteTimeLaplacian]; ring) hx
  change -nativeCoordinateLaplacian (finitePhysical s q) x = _ at h
  simp only [physicalForcing,zero_div,zero_mul,add_zero] at h
  have he : -8*cylinderLift (finiteAngular s (finiteTimeLaplacian q)) x / ‖x‖^2 / 8 =
      -(cylinderLift (finiteAngular s (finiteTimeLaplacian q)) x / ‖x‖^2) := by ring
  rw [he] at h
  exact neg_injective h

theorem native_finitePhysical_value_log_square (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (t : ℝ) :
    (∫ θ : S, Real.exp (-3*t)*finitePhysical s q (cylinderPoint (t,θ))^2 ∂angularVolume) =
      Real.exp (-2*t)*(∑ i ∈ s,q i t^2) := by
  have he (θ : S) : Real.exp (-3*t)*finitePhysical s q (cylinderPoint (t,θ))^2 =
      Real.exp (-2*t)*finiteAngular s q (t,θ)^2 := by
    rw [finitePhysical_eq_lift]
    change Real.exp (-3*t)*cylinderLift (finiteAngular s q) (Real.exp (-t) • (θ:E))^2 = _
    rw [cylinderLift_smul _ (Real.exp_pos _) θ,Real.log_exp,neg_neg,radialScale_exp_neg,mul_pow]
    rw [← mul_assoc]
    congr 1
    rw [pow_two,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_finiteAngular_square_eq_sum]

theorem native_finitePhysical_laplacian_log_square (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (hq : ∀ i ∈ s, ContDiff ℝ 2 (q i)) (t : ℝ) :
    (∫ θ : S, Real.exp (-3*t)*nativeCoordinateLaplacian (finitePhysical s q)
      (cylinderPoint (t,θ))^2 ∂angularVolume) =
        Real.exp (2*t)*(∑ i ∈ s,finiteTimeLaplacian q i t^2) := by
  have he (θ : S) : nativeCoordinateLaplacian (finitePhysical s q) (cylinderPoint (t,θ)) =
      Real.exp ((5/2:ℝ)*t)*finiteAngular s (finiteTimeLaplacian q) (t,θ) := by
    rw [native_finitePhysical_laplacian s q hq (cylinderPoint_ne_zero (t,θ)),cylinderPoint_norm]
    change cylinderLift (finiteAngular s (finiteTimeLaplacian q))
      (Real.exp (-t) • (θ:E)) / (Real.exp (-t))^2 = _
    rw [cylinderLift_smul _ (Real.exp_pos _) θ,Real.log_exp,neg_neg,radialScale_exp_neg]
    rw [mul_div_right_comm,pow_two,← Real.exp_add,← Real.exp_sub]
    congr 2
    ring
  simp_rw [he,mul_pow,← mul_assoc]
  have hexp : Real.exp (-3*t)*Real.exp ((5/2:ℝ)*t)^2 = Real.exp (2*t) := by
    rw [pow_two,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  rw [hexp,integral_const_mul,integral_finiteAngular_square_eq_sum]

#print axioms native_finitePhysical_laplacian
#print axioms native_finitePhysical_value_log_square
#print axioms native_finitePhysical_laplacian_log_square
end Yamabe3.Analysis.SpherePolar
