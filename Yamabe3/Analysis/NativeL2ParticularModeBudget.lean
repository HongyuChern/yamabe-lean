import Yamabe3.Analysis.NativeL2FiniteParticularCollar
import Yamabe3.Analysis.NativeC2CollarSeries

/-! A summable finite-mode physical collar budget for the same continuous
L2 source. Low auxiliary coordinates are explicitly omitted; the remaining
modes retain the genuine spherical Laplacian and original source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ →ᵇ ℝ)
  (hminus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)
  (F : ℝ →ᵇ SpectralSpace AngularIndex) (hF : MemLp F 2)

def nativeL2ParticularMode (i : AngularIndex) : E → ℝ :=
  if 6≤angularEigenvalue i then nativeL2FiniteParticular hκ0 hκ1 V hminus F {i} else 0

include hplus hF in
theorem nativeL2ParticularMode_C2 (i : AngularIndex) :
    ContDiffOn ℝ 2 (nativeL2ParticularMode hκ0 hκ1 V hminus F i) ({0}ᶜ : Set E) := by
  classical
  unfold nativeL2ParticularMode
  split_ifs with hi
  · exact (nativeL2FiniteParticular_collar_energy hκ0 hκ1 V hminus hplus F hF {i}
      (by intro j hj;simpa only [Finset.mem_singleton.mp hj] using hi)).1
  · exact contDiffOn_const

theorem nativeL2ParticularMode_sum (s : Finset AngularIndex) :
    (fun x => ∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hminus F i x)=
      nativeL2FiniteParticular hκ0 hκ1 V hminus F (s.filter (fun i => 6≤angularEigenvalue i)) := by
  classical
  funext x
  simp only [nativeL2ParticularMode,nativeL2FiniteParticular,finitePhysical,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp [finitePhysical]

def nativeL2ParticularModeBudget (i : AngularIndex) : ℝ :=
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num) nativeAngularRate_lower
    (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F
  Real.exp 6*(∫ t : ℝ,(U t i)^2)+Real.exp 2*(∫ t : ℝ,(F t i-V t*U t i)^2)

theorem nativeL2ParticularModeBudget_nonneg (i : AngularIndex) :
    0≤nativeL2ParticularModeBudget hκ0 hκ1 V hminus F i := by
  unfold nativeL2ParticularModeBudget
  positivity

include hplus hF in
theorem nativeL2ParticularModeBudget_summable :
    Summable (nativeL2ParticularModeBudget hκ0 hκ1 V hminus F) := by
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num : (0:ℝ)<5/2)
    nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F
  let G := fun t => F t-V t • U t
  obtain ⟨hU,hG,_,_⟩ := spectralIntegralPotentialInverse_actual_square_bounds nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus (by simpa only [neg_neg] using hplus) F hF
  have hu : Summable (fun i => ∫ t : ℝ,(U t i)^2) :=
    summable_of_sum_le (fun i => integral_nonneg (fun _ => sq_nonneg _))
      (spectralL2_finite_coordinate_integral_bound U hU)
  have hg : Summable (fun i => ∫ t : ℝ,(G t i)^2) :=
    summable_of_sum_le (fun i => integral_nonneg (fun _ => sq_nonneg _))
      (spectralL2_finite_coordinate_integral_bound G hG)
  exact (hu.mul_left (Real.exp 6)).add (hg.mul_left (Real.exp 2))

include hplus hF in
theorem nativeL2ParticularMode_finite_budget (s : Finset AngularIndex) :
    ((∫ x in nativePolarTimeWindow (Ioo (-1) 1),(∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hminus F i x)^2)+
      (∫ x in nativePolarTimeWindow (Ioo (-1) 1),nativeCoordinateLaplacian
        (fun y => ∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hminus F i y) x^2))≤
      ∑ i ∈ s,nativeL2ParticularModeBudget hκ0 hκ1 V hminus F i := by
  classical
  let U := spectralIntegralPotentialInverse nativeAngularRate (by norm_num : (0:ℝ)<5/2)
    nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F
  let G := fun t => F t-V t • U t
  let s' := s.filter (fun i => 6≤angularEigenvalue i)
  have hs (i : AngularIndex) (hi : i ∈ s') : 6≤angularEigenvalue i := (Finset.mem_filter.mp hi).2
  have ho (i : AngularIndex) := spectralIntegralPotentialInverse_physical_coordinate_C2 nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hminus F i
  obtain ⟨hU,hG,_,_⟩ := spectralIntegralPotentialInverse_actual_square_bounds nativeAngularRate
    (by norm_num : (0:ℝ)<5/2) nativeAngularRate_lower (by norm_num : |(-2:ℝ)|<5/2)
    hκ0 hκ1 V hminus (by simpa only [neg_neg] using hplus) F hF
  have he := native_finite_conjugated_collar_energy s' (fun i t => U t i) (fun i t => G t i)
    (fun i _ => (ho i).1) (fun i hi t => by
      change deriv (deriv (fun t => Real.exp (-2*t)*U t i)) t-
        (angularEigenvalue i+1/4)*(Real.exp (-2*t)*U t i)=Real.exp (-2*t)*(G t i)
      rw [←show nativeAngularRate i^2=angularEigenvalue i+1/4 by rw [nativeAngularRate_sq,max_eq_right (hs i hi)]]
      exact (ho i).2 t)
    (fun i _ => ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).comp_memLp' hU).integrable_sq)
    (fun i _ => ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).comp_memLp' hG).integrable_sq)
  have hsum : Real.exp 6*(∑ i ∈ s',∫ t : ℝ,(U t i)^2)+Real.exp 2*(∑ i ∈ s',∫ t : ℝ,(G t i)^2)=
      ∑ i ∈ s',nativeL2ParticularModeBudget hκ0 hκ1 V hminus F i := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    rfl
  have hsub : (∑ i ∈ s',nativeL2ParticularModeBudget hκ0 hκ1 V hminus F i)≤
      ∑ i ∈ s,nativeL2ParticularModeBudget hκ0 hκ1 V hminus F i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => nativeL2ParticularModeBudget_nonneg hκ0 hκ1 V hminus F i)
  have hfun := nativeL2ParticularMode_sum hκ0 hκ1 V hminus F s
  have hval : (fun x => (∑ i ∈ s,nativeL2ParticularMode hκ0 hκ1 V hminus F i x)^2)=
      fun x => (nativeL2FiniteParticular hκ0 hκ1 V hminus F s' x)^2 :=
    funext fun x => congrArg (fun a : ℝ => a^2) (congrFun hfun x)
  rw [hval,hfun]
  exact he.2.2.2.trans (hsum.trans_le hsub)

#print axioms nativeL2ParticularMode_C2
#print axioms nativeL2ParticularMode_sum
#print axioms nativeL2ParticularModeBudget_summable
#print axioms nativeL2ParticularMode_finite_budget
end Yamabe3.Analysis.SpherePolar
