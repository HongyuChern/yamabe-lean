import Yamabe3.Analysis.NativeManifoldC1Green
import Yamabe3.Analysis.NativeAngularHalfRegularity

/-! The original C1 angular function is proved to have finite native
H1 spectral energy. Finite smooth eigenfunctions test the C1 Green identity;
positivity pays the complete gradient energy, without assuming density. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace lp
namespace Yamabe3.Analysis.SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm
open Yamabe3.Analysis.NativeC1Green Yamabe3.Analysis.Delaunay
private abbrev D := (roundSphereMetric 2).leviCivitaData
private abbrev g := roundSphereMetric 2
private abbrev μ := (roundSphereMetric 2).volumeMeasure

def continuousAngularL2 (f : UnitSphere 2 → ℝ) (hf : Continuous f) : AngularL2 :=
  ((hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)).restrict univ).toLp f

theorem continuousAngularL2_ae (f : UnitSphere 2 → ℝ) (hf : Continuous f) :
    ⇑(continuousAngularL2 f hf) =ᵐ[μ] f := by
  have h : ⇑(continuousAngularL2 f hf)=ᵐ[μ.restrict univ] f :=
    ((hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)).restrict univ).coeFn_toLp
  simpa only [Measure.restrict_univ] using h

def angularC1Pair (f h : UnitSphere 2 → ℝ) : ℝ :=
  (∫ x,f x*h x ∂μ)+(∫ x,g.inner x (D.gradient f x) (D.gradient h x) ∂μ)

theorem angularC1Pair_symm (f h : UnitSphere 2 → ℝ) :
    angularC1Pair f h=angularC1Pair h f := by
  unfold angularC1Pair
  congr 1
  · exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  · exact integral_congr_ae (Eventually.of_forall fun x => g.symm x _ _)

theorem angularC1Pair_finset_right {ι : Type*} (s : Finset ι)
    {f : UnitSphere 2 → ℝ} {h : ι → UnitSphere 2 → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 f)
    (hh : ∀ i∈s,ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 (h i)) :
    angularC1Pair f (fun x=>∑ i∈s,h i x)=∑ i∈s,angularC1Pair f (h i) := by
  have hg (x) := D.gradient_finset_sum s h x (fun i hi => (hh i hi x).mdifferentiableAt (by simp))
  have hmul (i) (hi : i∈s) : Integrable (fun x=>f x*h i x) μ :=
    (hf.continuous.mul (hh i hi).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (i) (hi : i∈s) := integrable_inner_gradient_C1 D hf (hh i hi) (HasCompactSupport.of_compactSpace _)
  simp only [angularC1Pair,Finset.mul_sum,hg,map_sum]
  rw [integral_finsetSum _ hmul,integral_finsetSum _ hp,Finset.sum_add_distrib]

theorem angularC1Pair_smul_right (c : ℝ) (f h : UnitSphere 2 → ℝ) :
    angularC1Pair f (fun x=>c*h x)=c*angularC1Pair f h := by
  have hg (x) : D.gradient (fun y=>c*h y) x=c • D.gradient h x := by
    apply (g.inner_isInvertible x).injective
    ext v
    simp only [D.inner_gradient,mvfderiv_const_mul,map_smul,smul_apply,smul_eq_mul]
  unfold angularC1Pair
  simp only [hg,map_smul,smul_eq_mul]
  have hm : (fun x=>f x*(c*h x))=(fun x=>c*(f x*h x)) := by funext x;ring
  rw [hm,integral_const_mul,integral_const_mul]
  ring

theorem angularC1Pair_bessel_inequality {f h : UnitSphere 2 → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 f)
    (hh : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 h) :
    2*angularC1Pair f h-angularC1Pair h h ≤ angularC1Pair f f := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitSphere 2 → Type _) := ⟨g.toRiemannianMetric⟩
  let e (u v : UnitSphere 2 → ℝ) (x) := u x*v x+g.inner x (D.gradient u x) (D.gradient v x)
  have he (u v) (hu : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 u) (hv : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 v) :
      Integrable (e u v) μ :=
    ((hu.continuous.mul hv.continuous).add (continuous_inner_gradient_C1 D hu hv)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq (u v) (hu : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 u) (hv : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 v) :
      (∫x,e u v x ∂μ)=angularC1Pair u v := by
    exact integral_add ((hu.continuous.mul hv.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (integrable_inner_gradient_C1 D hu hv (HasCompactSupport.of_compactSpace _))
  have hineq := integral_mono ((he f h hf hh).const_mul 2 |>.sub (he h h hh hh)) (he f f hf hf) (fun x => by
    have hg : 0 ≤ inner ℝ (D.gradient f x-D.gradient h x) (D.gradient f x-D.gradient h x) := real_inner_self_nonneg
    rw [inner_sub_left,inner_sub_right,inner_sub_right] at hg
    have hcomm : inner ℝ (D.gradient h x) (D.gradient f x)=inner ℝ (D.gradient f x) (D.gradient h x) := real_inner_comm _ _
    rw [hcomm] at hg
    change 2*(f x*h x+inner ℝ (D.gradient f x) (D.gradient h x))-
      (h x*h x+inner ℝ (D.gradient h x) (D.gradient h x)) ≤ f x*f x+inner ℝ (D.gradient f x) (D.gradient f x)
    nlinarith only [hg,sq_nonneg (f x-h x)])
  simp only [Pi.sub_apply] at hineq
  rw [integral_sub ((he f h hf hh).const_mul 2) (he h h hh hh),integral_const_mul,
    heq f h hf hh,heq h h hh hh,heq f f hf hf] at hineq
  exact hineq

theorem angularC1Pair_eigenfunction {f U : UnitSphere 2 → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 f) (i : AngularIndex)
    (hU : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ U)
    (hae : U =ᵐ[μ] ⇑(angularBasis i))
    (he : ∀ x,-D.laplacian U x=angularEigenvalue i*U x) :
    angularC1Pair f U=(1+angularEigenvalue i)*inner ℝ (angularBasis i) (continuousAngularL2 f hf.continuous) := by
  have hgreen := integral_mul_laplacian_of_compact_C1_test D hf hU (HasCompactSupport.of_compactSpace _)
  have hlap : (∫x,f x*D.laplacian U x ∂μ)= -angularEigenvalue i*(∫x,f x*U x ∂μ) := by
    have heq : (fun x=>f x*D.laplacian U x)=(fun x=> -angularEigenvalue i*(f x*U x)) := by
      funext x
      rw [show D.laplacian U x= -(angularEigenvalue i*U x) by linarith only [he x]]
      ring
    rw [heq,integral_const_mul]
  have hi : inner ℝ (angularBasis i) (continuousAngularL2 f hf.continuous)=(∫x,f x*U x ∂μ) := by
    rw [L2.inner_def,setIntegral_univ]
    apply integral_congr_ae
    filter_upwards [hae,continuousAngularL2_ae f hf.continuous] with x hx hfx
    rw [←hx,hfx]
    simp [mul_comm]
  rw [hi]
  unfold angularC1Pair
  rw [hlap] at hgreen
  nlinarith only [hgreen]

theorem angular_C1_finite_energy_bound (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 f) (s : Finset AngularIndex) :
    (∑i∈s,(1+angularEigenvalue i)*(inner ℝ (angularBasis i) (continuousAngularL2 f hf.continuous))^2) ≤ 
      angularC1Pair f f := by
  classical
  choose U hU hUae hne hUE using exists_smooth_angular_eigenfunction
  let c (i) := inner ℝ (angularBasis i) (continuousAngularL2 f hf.continuous)
  let w : UnitSphere 2 → ℝ := fun x=>∑i∈s,c i*U i x
  have hw : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ w := ContMDiff.sum fun i _=>contMDiff_const.mul (hU i)
  have hUL (i) : continuousAngularL2 (U i) (hU i).continuous=angularBasis i := by
    apply Lp.ext
    simpa only [Measure.restrict_univ] using (continuousAngularL2_ae _ _).trans (hUae i)
  have hwL : continuousAngularL2 w hw.continuous=∑i∈s,c i • angularBasis i := by
    apply Lp.ext
    have hc := Lp.coeFn_finsetSum s (fun i=>c i • angularBasis i)
    have hsm : ∀ i, ⇑(c i • angularBasis i)=ᵐ[μ] (fun x=>c i*(angularBasis i) x) :=
      fun i=>by
        filter_upwards [(ae_restrict_iff' MeasurableSet.univ).mp (Lp.coeFn_smul (c i) (angularBasis i))] with x hx
        exact hx (mem_univ x)
    have he : ⇑(continuousAngularL2 w hw.continuous)=ᵐ[μ] ⇑(∑i∈s,c i • angularBasis i) := by
      filter_upwards [continuousAngularL2_ae w hw.continuous,
        (Finset.eventually_all s).mpr (fun i _=>hUae i),(Finset.eventually_all s).mpr (fun i _=>hsm i),
        (show ⇑(∑i∈s,c i • angularBasis i)=ᵐ[μ] (fun x=>∑i∈s,(c i • angularBasis i) x) by
          filter_upwards [(ae_restrict_iff' MeasurableSet.univ).mp hc] with x hx
          simpa only [Finset.sum_apply] using hx (mem_univ x))] with x hx hux hsx hcx
      rw [hx,hcx]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hsx i hi,hux i hi]
    simpa only [Measure.restrict_univ] using he
  have hcW (i) (hi : i∈s) : inner ℝ (angularBasis i) (continuousAngularL2 w hw.continuous)=c i := by
    rw [hwL,inner_sum]
    simp_rw [real_inner_smul_right,orthonormal_iff_ite.mp angularBasis.orthonormal]
    simp [hi]
  have hpair (a) (ha : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 a) :
      angularC1Pair a w=∑i∈s,c i*((1+angularEigenvalue i)*inner ℝ (angularBasis i) (continuousAngularL2 a ha.continuous)) := by
    rw [show w=(fun x=>∑i∈s,c i*U i x) from rfl,angularC1Pair_finset_right s (h := fun i x=>c i*U i x) ha (fun i _=>contMDiff_const.mul ((hU i).of_le (by simp)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [angularC1Pair_smul_right,angularC1Pair_eigenfunction ha i (hU i) (hUae i) (hUE i)]
  have hfw : angularC1Pair f w=∑i∈s,(1+angularEigenvalue i)*(c i)^2 := by
    rw [hpair f hf]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [c]
    ring
  have hww : angularC1Pair w w=∑i∈s,(1+angularEigenvalue i)*(c i)^2 := by
    rw [hpair w (hw.of_le (by simp))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcW i hi]
    ring
  have h := angularC1Pair_bessel_inequality hf (hw.of_le (by simp))
  rw [hfw,hww] at h
  exact (by linarith only [h])

#print axioms continuousAngularL2_ae
#print axioms angularC1Pair_bessel_inequality
#print axioms angularC1Pair_eigenfunction
#print axioms angular_C1_finite_energy_bound
end Yamabe3.Analysis.SphereSpectrum
