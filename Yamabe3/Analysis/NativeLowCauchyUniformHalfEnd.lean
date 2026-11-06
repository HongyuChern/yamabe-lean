import Yamabe3.Analysis.NativeLowCauchyHalfLineBound
import Yamabe3.Analysis.NativeFiniteHalfEndBound

/-! The actual finite low Cauchy jet has a uniform exterior half-end H2
bound. Constants depend on the fixed entrance phase and precede all
low Cauchy coordinates and scales. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeLowCauchyAllScaleJet {τ : ℝ} (ht : 0<τ) (v : NativeLowCauchyCoordinates) (s : ℝ) :
    nativeCollarJetClosure :=
  nativeFiniteAllScaleJet nativeLowIndexFinset (fun i t => nativeLowCauchyQ ht v i (τ+t))
    (fun i hi => (nativeLowCauchyQ_C2 ht v i hi).comp (contDiff_const.add contDiff_id)) s

theorem exists_nativeLowCauchy_uniform_halfEnd_bound {τ : ℝ} (ht : 0<τ) :
    ∃C : ℝ,0≤C ∧ ∀(v : NativeLowCauchyCoordinates) (s : ℝ),s≤0 →
      ‖nativeLowCauchyAllScaleJet ht v s‖≤C*‖v‖ := by
  classical
  let M : AngularIndex→ℝ := fun i => if hi : i∈nativeLowIndexFinset then
    (bubbleLowZeroCauchyLinear_halfLine_bound i hi ht (τ+1)).choose else 0
  have hM (i : AngularIndex) (hi : i∈nativeLowIndexFinset) : 0≤M i := by
    dsimp only [M];rw [dif_pos hi]
    exact (bubbleLowZeroCauchyLinear_halfLine_bound i hi ht (τ+1)).choose_spec.1
  have hb (i : AngularIndex) (hi : i∈nativeLowIndexFinset) (v : NativeLowCauchyCoordinates)
      (t : ℝ) (hc : t≤τ+1) :
      ‖nativeLowCauchyQ ht v i t‖≤M i*‖v‖ ∧
        ‖deriv (deriv (nativeLowCauchyQ ht v i)) t‖≤M i*‖v‖ := by
    have h := (bubbleLowZeroCauchyLinear_halfLine_bound i hi ht (τ+1)).choose_spec.2
      (v ⟨i,hi⟩).1 (v ⟨i,hi⟩).2 t hc
    have hm : (bubbleLowZeroCauchyLinear_halfLine_bound i hi ht (τ+1)).choose=M i := by
      dsimp only [M];rw [dif_pos hi]
    rw [hm] at h
    have hn : max ‖(v ⟨i,hi⟩).1‖ ‖(v ⟨i,hi⟩).2‖≤‖v‖ := by
      simpa only [Prod.norm_def] using norm_le_pi_norm v ⟨i,hi⟩
    rw [nativeLowCauchyQ,dif_pos hi]
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_left hn (hM i hi)),
      h.2.2.trans (mul_le_mul_of_nonneg_left hn (hM i hi))⟩
  obtain ⟨D,hD,hd⟩ := exists_nativeFinite_halfEnd_H2_bound
  let B := ∑i∈nativeLowIndexFinset,((M i)^2+2*((M i)^2+angularEnergyWeight i^4*(M i)^2))
  have hB : 0≤B := by unfold B;exact Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨Real.sqrt (D*B),Real.sqrt_nonneg _,fun v s hs => ?_⟩
  let q := fun i t => nativeLowCauchyQ ht v i (τ+t)
  have hq (i : AngularIndex) (hi : i∈nativeLowIndexFinset) : ContDiff ℝ 2 (q i) :=
    (nativeLowCauchyQ_C2 ht v i hi).comp (contDiff_const.add contDiff_id)
  have h0 (i : AngularIndex) (hi : i∈nativeLowIndexFinset) (t : ℝ) (hc : t≤1) :
      ‖q i t‖≤(M i)*‖v‖ := (hb i hi v (τ+t) (by linarith)).1
  have h2 (i : AngularIndex) (hi : i∈nativeLowIndexFinset) (t : ℝ) (hc : t≤1) :
      ‖deriv (deriv (q i)) t‖≤(M i)*‖v‖ := by
    have he : deriv (deriv (q i)) t=deriv (deriv (nativeLowCauchyQ ht v i)) (τ+t) := by
      have hd : deriv (q i)=fun t => deriv (nativeLowCauchyQ ht v i) (τ+t) :=
        funext (fun t => deriv_comp_const_add (nativeLowCauchyQ ht v i) τ t)
      rw [hd,deriv_comp_const_add]
    rw [he]
    exact (hb i hi v (τ+t) (by linarith)).2
  have h := hd nativeLowIndexFinset q hq (fun i => M i*‖v‖) (fun i => M i*‖v‖)
    (fun i hi => mul_nonneg (hM i hi) (norm_nonneg _))
    (fun i hi => mul_nonneg (hM i hi) (norm_nonneg _)) h0 h2 s hs
  have hsum : (∑i∈nativeLowIndexFinset,((M i*‖v‖)^2+2*((M i*‖v‖)^2+
      angularEnergyWeight i^4*(M i*‖v‖)^2)))=B*‖v‖^2 := by
    dsimp only [B]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi;ring
  rw [hsum] at h
  have hex : Real.exp (4*s)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hh : ‖nativeLowCauchyAllScaleJet ht v s‖^2≤(D*B)*‖v‖^2 :=
    h.trans ((mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hD hex)
      (mul_nonneg hB (sq_nonneg _))).trans_eq (by ring))
  have hsqrt : (Real.sqrt (D*B)*‖v‖)^2=(D*B)*‖v‖^2 := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hD hB)]
  have hn : 0≤Real.sqrt (D*B)*‖v‖ := by positivity
  nlinarith only [hh,hsqrt,norm_nonneg (nativeLowCauchyAllScaleJet ht v s),hn]

#print axioms exists_nativeLowCauchy_uniform_halfEnd_bound
end Yamabe3.Analysis.SpherePolar
