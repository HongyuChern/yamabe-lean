import Yamabe3.Analysis.DelaunayCauchyKernel

/-! Opposite exponential weights for the same reflection-symmetric
potential. Reflection is proved for the original Cauchy orbit, not supplied
as a replacement orbit or as an extra main assumption. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Yamabe3.Analysis.Delaunay

theorem spectralMajorant_reverse (k δ s : ℝ) :
    spectralMajorant k (-δ) (-s) = spectralMajorant k δ s := by
  unfold spectralMajorant
  rw [abs_neg]
  congr 2
  ring

theorem spectral_potential_integral_reflection (k δ c t : ℝ) (V : ℝ → ℝ)
    (hV : ∀ x,V (2*c-x)=V x) :
    (∫ s : ℝ,spectralMajorant k (-δ) s * V (t-s)) =
      ∫ s : ℝ,spectralMajorant k δ s * V ((2*c-t)-s) := by
  rw [← integral_neg_eq_self (fun s : ℝ => spectralMajorant k (-δ) s * V (t-s))]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    dsimp only
    rw [spectralMajorant_reverse]
    have h := hV (t-(-s))
    rw [show 2*c-(t-(-s))=(2*c-t)-s by ring] at h
    rw [h]

theorem exists_same_cauchy_orbit_reflection_center {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hode : ∀ t,deriv (deriv v) t=radialForce (v t))
    (hm : 0<v 0) {q : ℝ} (hq : 0<q) (hsmall : q<3/8)
    (henergy : q=v 0^2-v 0^6-4*deriv v 0^2) :
    ∃ c : ℝ,∀ t,v (2*c-t)=v t := by
  obtain ⟨η,w,τ,hη,hηsmall,hE,hlo,hup,hw,hw0,hd0,hb,heq,hvEq,hmin⟩ :=
    exists_same_cauchy_orbit_neck_phase hv hode hm hq hsmall henergy
  have hev := radial_neck_solution_even hw heq hd0
  refine ⟨-τ,fun t => ?_⟩
  rw [hvEq]
  change w (2*(-τ)-t+τ)=w (t+τ)
  rw [show 2*(-τ)-t+τ=-(t+τ) by ring]
  exact hev _

/-- Both weights use one strict constant and the original orbit. -/
theorem exists_uniform_small_energy_two_weight_kernel_bound :
    ∃ (κ q₀ : ℝ),0 ≤ κ ∧ κ<1 ∧ 0<q₀ ∧
      ∀ (v : ℝ → ℝ),ContDiff ℝ ∞ v →
      (∀ t,deriv (deriv v) t=radialForce (v t)) → 0<v 0 →
      ∀ q : ℝ,0<q → q<q₀ → q=v 0^2-v 0^6-4*deriv v 0^2 →
      (∀ t,0 ≤ v t ∧ v t ≤ 1) ∧
      (∀ t,(∫ s : ℝ,spectralMajorant (5/2) (-2) s*((15/4)*v (t-s)^4)) ≤ κ) ∧
      (∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*((15/4)*v (t-s)^4)) ≤ κ) := by
  obtain ⟨κ,q₁,hκ,hκ1,hq₁,hb⟩ := exists_uniform_small_energy_same_orbit_kernel_bound
  refine ⟨κ,min q₁ (3/8),hκ,hκ1,lt_min hq₁ (by norm_num),?_⟩
  intro v hv heq hm q hq hsmall hE
  obtain ⟨hvbd,hminus⟩ := hb v hv heq hm q hq (hsmall.trans_le (min_le_left _ _)) hE
  obtain ⟨c,hc⟩ := exists_same_cauchy_orbit_reflection_center hv heq hm hq
    (hsmall.trans_le (min_le_right _ _)) hE
  refine ⟨hvbd,hminus,fun t => ?_⟩
  have hi := spectral_potential_integral_reflection (5/2) (-2) c t
    (fun x => (15/4)*v x^4) (fun x => by rw [hc])
  norm_num only [neg_neg] at hi
  rw [hi]
  exact hminus _

#print axioms spectral_potential_integral_reflection
#print axioms exists_same_cauchy_orbit_reflection_center
#print axioms exists_uniform_small_energy_two_weight_kernel_bound
end Yamabe3.Analysis.Delaunay
