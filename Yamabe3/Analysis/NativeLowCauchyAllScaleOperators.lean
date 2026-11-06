import Yamabe3.Analysis.NativeLowCauchyUniformHalfEnd
import Yamabe3.Analysis.NativeCollarJetValueInjective

/-! The actual finite compensated low Cauchy field is a bounded LINEAR
H2 jet at every exterior scale. Its original two Cauchy data, finite
coefficients and same physical representative are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic

private theorem q_add {t₀ : ℝ} (ht : 0<t₀) (v w : NativeLowCauchyCoordinates) (i : AngularIndex) :
    nativeLowCauchyQ ht (v+w) i=nativeLowCauchyQ ht v i+nativeLowCauchyQ ht w i := by
  by_cases hi : i∈nativeLowIndexFinset
  · simp only [nativeLowCauchyQ,dif_pos hi,Pi.add_apply,map_add]
  · simp only [nativeLowCauchyQ,dif_neg hi,add_zero]

private theorem q_smul {t₀ : ℝ} (ht : 0<t₀) (c : ℝ) (v : NativeLowCauchyCoordinates) (i : AngularIndex) :
    nativeLowCauchyQ ht (c • v) i=c • nativeLowCauchyQ ht v i := by
  by_cases hi : i∈nativeLowIndexFinset
  · simp only [nativeLowCauchyQ,dif_pos hi,Pi.smul_apply,map_smul]
  · simp only [nativeLowCauchyQ,dif_neg hi,smul_zero]

private def physicalLinear {t₀ : ℝ} (ht : 0<t₀) : NativeLowCauchyCoordinates →ₗ[ℝ] (E→ℝ) where
  toFun v := finitePhysical nativeLowIndexFinset (fun i t => nativeLowCauchyQ ht v i (t₀+t))
  map_add' v w := by
    funext x
    simp only [finitePhysical,Pi.add_apply,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x=0
    · subst x; simp only [cylinderLift_zero,add_zero]
    · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
      change cylinderLift _ (y:E)=cylinderLift _ (y:E)+cylinderLift _ (y:E)
      simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,q_add,Pi.add_apply]
      ring
  map_smul' c v := by
    funext x
    simp only [finitePhysical,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x=0
    · subst x; simp only [cylinderLift_zero,mul_zero]
    · let y : puncturedSpace := ⟨x,by change x≠0;exact hx⟩
      change cylinderLift _ (y:E)=c*cylinderLift _ (y:E)
      simp only [cylinderLift_coe,puncturedCylinderLift,separableCylinder,q_smul,Pi.smul_apply,smul_eq_mul]
      ring

def nativeLowCauchyAllScaleJetLinear {τ:ℝ} (ht:0<τ) (s:ℝ) :
    NativeLowCauchyCoordinates →ₗ[ℝ] nativeCollarJetClosure where
  toFun v:=nativeLowCauchyAllScaleJet ht v s
  map_add' v w:=by
    apply nativeCollarJet_value_injective
    apply Lp.ext
    have hv:=nativeFiniteAllScaleJet_same_field nativeLowIndexFinset
      (fun i t=>nativeLowCauchyQ ht v i (τ+t))
      (fun i hi=>(nativeLowCauchyQ_C2 ht v i hi).comp (contDiff_const.add contDiff_id)) s
    have hw:=nativeFiniteAllScaleJet_same_field nativeLowIndexFinset
      (fun i t=>nativeLowCauchyQ ht w i (τ+t))
      (fun i hi=>(nativeLowCauchyQ_C2 ht w i hi).comp (contDiff_const.add contDiff_id)) s
    have hsum:=nativeFiniteAllScaleJet_same_field nativeLowIndexFinset
      (fun i t=>nativeLowCauchyQ ht (v+w) i (τ+t))
      (fun i hi=>(nativeLowCauchyQ_C2 ht (v+w) i hi).comp (contDiff_const.add contDiff_id)) s
    filter_upwards [hv,hw,hsum,Lp.coeFn_add (nativeLowCauchyAllScaleJet ht v s).val.1
      (nativeLowCauchyAllScaleJet ht w s).val.1] with x hv hw hh ha
    change (nativeLowCauchyAllScaleJet ht (v+w) s).val.1 x=
      ((nativeLowCauchyAllScaleJet ht v s).val.1+(nativeLowCauchyAllScaleJet ht w s).val.1:NativeCollarL2) x
    rw [ha]
    change _=(nativeLowCauchyAllScaleJet ht v s).val.1 x+(nativeLowCauchyAllScaleJet ht w s).val.1 x
    change (nativeLowCauchyAllScaleJet ht (v+w) s).val.1 x=Real.exp (3*s/2)*physicalLinear ht (v+w) (Real.exp (-s) • x) at hh
    change (nativeLowCauchyAllScaleJet ht v s).val.1 x=Real.exp (3*s/2)*physicalLinear ht v (Real.exp (-s) • x) at hv
    change (nativeLowCauchyAllScaleJet ht w s).val.1 x=Real.exp (3*s/2)*physicalLinear ht w (Real.exp (-s) • x) at hw
    rw [hh,hv,hw]
    change Real.exp (3*s/2)*physicalLinear ht (v+w) (Real.exp (-s) • x)=
      Real.exp (3*s/2)*physicalLinear ht v (Real.exp (-s) • x)+
        Real.exp (3*s/2)*physicalLinear ht w (Real.exp (-s) • x)
    rw [map_add]
    simp only [Pi.add_apply,mul_add]
  map_smul' c v:=by
    apply nativeCollarJet_value_injective
    apply Lp.ext
    have hv:=nativeFiniteAllScaleJet_same_field nativeLowIndexFinset
      (fun i t=>nativeLowCauchyQ ht v i (τ+t))
      (fun i hi=>(nativeLowCauchyQ_C2 ht v i hi).comp (contDiff_const.add contDiff_id)) s
    have hcv:=nativeFiniteAllScaleJet_same_field nativeLowIndexFinset
      (fun i t=>nativeLowCauchyQ ht (c • v) i (τ+t))
      (fun i hi=>(nativeLowCauchyQ_C2 ht (c • v) i hi).comp (contDiff_const.add contDiff_id)) s
    filter_upwards [hv,hcv,Lp.coeFn_smul c (nativeLowCauchyAllScaleJet ht v s).val.1] with x hv hh ha
    change (nativeLowCauchyAllScaleJet ht (c • v) s).val.1 x=
      (c • (nativeLowCauchyAllScaleJet ht v s).val.1:NativeCollarL2) x
    rw [ha]
    change _=c*(nativeLowCauchyAllScaleJet ht v s).val.1 x
    change (nativeLowCauchyAllScaleJet ht (c • v) s).val.1 x=Real.exp (3*s/2)*physicalLinear ht (c • v) (Real.exp (-s) • x) at hh
    change (nativeLowCauchyAllScaleJet ht v s).val.1 x=Real.exp (3*s/2)*physicalLinear ht v (Real.exp (-s) • x) at hv
    rw [hh,hv]
    change Real.exp (3*s/2)*physicalLinear ht (c • v) (Real.exp (-s) • x)=
      c*(Real.exp (3*s/2)*physicalLinear ht v (Real.exp (-s) • x))
    rw [map_smul]
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

theorem exists_nativeLowCauchyAllScaleJetCLM {τ:ℝ} (ht:0<τ) :
    ∃C:ℝ,0≤C ∧ ∀s:ℝ,s≤0 →
      ∃J:NativeLowCauchyCoordinates →L[ℝ] nativeCollarJetClosure,‖J‖≤C ∧
        ∀v,J v=nativeLowCauchyAllScaleJet ht v s := by
  obtain ⟨C,hC,hb⟩:=exists_nativeLowCauchy_uniform_halfEnd_bound ht
  refine ⟨C,hC,?_⟩
  intro s hs
  let L:=nativeLowCauchyAllScaleJetLinear ht s
  have hL v:‖L v‖≤C*‖v‖:=hb v s hs
  exact ⟨L.mkContinuous C hL,LinearMap.mkContinuous_norm_le _ hC hL,fun v=>rfl⟩

#print axioms nativeLowCauchyAllScaleJetLinear
#print axioms exists_nativeLowCauchyAllScaleJetCLM
end Yamabe3.Analysis.SpherePolar
