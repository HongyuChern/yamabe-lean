import Yamabe3.Analysis.BubbleLowAngularCauchy

/-! A linear choice of the actual compensated zero-source low Cauchy
solution. Only two already constructed unit-data solutions are chosen;
all later data use their linear combination, with the same compensation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

private theorem zero_source_exists (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {t₀ : ℝ} (ht : 0<t₀) (d n : ℝ) :
    ∃q : ℝ→ℝ, ContDiff ℝ 2 q ∧
      (∀t,deriv (deriv q) t-bubbleLowCoefficient i t*q t=
        -bubbleLowCauchyCompensation i t₀ d n 0*bubbleCompensation i t) ∧
      q t₀=d ∧ deriv q t₀=n ∧
      Tendsto q atBot (𝓝 0) ∧ Tendsto (deriv q) atBot (𝓝 0) := by
  obtain ⟨c,q,hc,hq,he,hd,hn,hb,hdb⟩ :=
    exists_actual_bubble_low_cauchy_solver i hi (0 : ℝ →ᵇ ℝ) ht d n
  have hm : bubbleLowSourceMoment i (0 : ℝ →ᵇ ℝ) t₀=0 := by
    simp [bubbleLowSourceMoment]
  rw [hm] at hc
  subst c
  refine ⟨q,hq,?_,hd,hn,hb,hdb⟩
  intro t
  simpa using he t

private def unitField (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {t₀ : ℝ} (ht : 0<t₀) (d n : ℝ) : ℝ→ℝ :=
  (zero_source_exists i hi ht d n).choose

private theorem unitField_spec (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {t₀ : ℝ} (ht : 0<t₀) (d n : ℝ) :
    let q := unitField i hi ht d n
    ContDiff ℝ 2 q ∧
      (∀t,deriv (deriv q) t-bubbleLowCoefficient i t*q t=
        -bubbleLowCauchyCompensation i t₀ d n 0*bubbleCompensation i t) ∧
      q t₀=d ∧ deriv q t₀=n ∧
      Tendsto q atBot (𝓝 0) ∧ Tendsto (deriv q) atBot (𝓝 0) :=
  (zero_source_exists i hi ht d n).choose_spec

/-- Linear in both actual entrance data; no compatibility is imposed. -/
def bubbleLowZeroCauchyLinear (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {t₀ : ℝ} (ht : 0<t₀) : (ℝ×ℝ) →ₗ[ℝ] (ℝ→ℝ) where
  toFun v := fun t => v.1*unitField i hi ht 1 0 t+v.2*unitField i hi ht 0 1 t
  map_add' v w := by ext t; simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply]; ring
  map_smul' c v := by ext t; simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Pi.smul_apply,RingHom.id_apply]; ring

theorem bubbleLowZeroCauchyLinear_spec (i : AngularIndex) (hi : i∈nativeLowIndexFinset)
    {t₀ : ℝ} (ht : 0<t₀) (d n : ℝ) :
    let q := bubbleLowZeroCauchyLinear i hi ht (d,n)
    ContDiff ℝ 2 q ∧
      (∀t,deriv (deriv q) t-bubbleLowCoefficient i t*q t=
        -bubbleLowCauchyCompensation i t₀ d n 0*bubbleCompensation i t) ∧
      q t₀=d ∧ deriv q t₀=n ∧
      Tendsto q atBot (𝓝 0) ∧ Tendsto (deriv q) atBot (𝓝 0) := by
  let a := unitField i hi ht 1 0
  let b := unitField i hi ht 0 1
  have ha := unitField_spec i hi ht 1 0
  have hb := unitField_spec i hi ht 0 1
  change ContDiff ℝ 2 a ∧ _ at ha
  change ContDiff ℝ 2 b ∧ _ at hb
  have hd (t : ℝ) : deriv (fun s => d*a s+n*b s) t=d*deriv a t+n*deriv b t :=
    (((ha.1.differentiable (by norm_num) t).hasDerivAt.const_mul d).add
      ((hb.1.differentiable (by norm_num) t).hasDerivAt.const_mul n)).deriv
  have hdd (t : ℝ) : deriv (deriv (fun s => d*a s+n*b s)) t=
      d*deriv (deriv a) t+n*deriv (deriv b) t := by
    rw [show deriv (fun s => d*a s+n*b s)=fun t => d*deriv a t+n*deriv b t from funext hd]
    exact (((ha.1.differentiable_deriv_two t).hasDerivAt.const_mul d).add
      ((hb.1.differentiable_deriv_two t).hasDerivAt.const_mul n)).deriv
  change ContDiff ℝ 2 (fun t => d*a t+n*b t) ∧ _
  refine ⟨(contDiff_const.mul ha.1).add (contDiff_const.mul hb.1),?_,?_,?_,?_,?_⟩
  · intro t
    change deriv (deriv (fun s => d*a s+n*b s)) t-
      bubbleLowCoefficient i t*(d*a t+n*b t)=_
    rw [hdd]
    have heA := ha.2.1 t
    have heB := hb.2.1 t
    have hc : bubbleLowCauchyCompensation i t₀ d n 0=
        d*bubbleLowCauchyCompensation i t₀ 1 0 0+
        n*bubbleLowCauchyCompensation i t₀ 0 1 0 := by
      unfold bubbleLowCauchyCompensation
      ring
    rw [hc]
    linear_combination d*heA+n*heB
  · change d*a t₀+n*b t₀=d
    dsimp only [a,b]
    rw [ha.2.2.1,hb.2.2.1]; ring
  · change deriv (fun s => d*a s+n*b s) t₀=n
    rw [hd,ha.2.2.2.1,hb.2.2.2.1]; ring
  · change Tendsto (fun t => d*a t+n*b t) atBot (𝓝 0)
    simpa only [mul_zero,add_zero] using
      (ha.2.2.2.2.1.const_mul d).add (hb.2.2.2.2.1.const_mul n)
  · change Tendsto (deriv (fun s => d*a s+n*b s)) atBot (𝓝 0)
    rw [show deriv (fun s => d*a s+n*b s)=fun t => d*deriv a t+n*deriv b t from funext hd]
    simpa only [mul_zero,add_zero] using
      (ha.2.2.2.2.2.const_mul d).add (hb.2.2.2.2.2.const_mul n)

#print axioms bubbleLowZeroCauchyLinear_spec
end Yamabe3.Analysis.Delaunay
