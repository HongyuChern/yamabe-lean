import Yamabe3.Analysis.NativeFiniteCollarTrace
import Yamabe3.Analysis.BubbleLowAngularCauchy

/-! The finite low exterior correction is realized as one actual H2
collar with both genuine boundary traces, in entrance-centred time. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeBubbleLowCollarJet (t₀ : ℝ) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)) : nativeCollarJetClosure :=
  nativeFiniteCollarJet nativeLowIndexFinset (fun i t => q i (t₀+t))
    (fun i hi => (hq i hi).comp (contDiff_const.add contDiff_id))

theorem nativeBubbleLowCollarJet_value_trace (t₀ : ℝ) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)) :
    nativeCollarValueTraceCLM (nativeBubbleLowCollarJet t₀ q hq)=
      nativeAngularTraceCLM (bubbleLowAngularCurve q t₀) := by
  unfold nativeBubbleLowCollarJet
  rw [nativeFiniteCollarJet_value_trace]
  simp only [add_zero,bubbleLowAngularCurve]

theorem nativeBubbleLowCollarJet_normal_trace (t₀ : ℝ) (q : AngularIndex → ℝ → ℝ)
    (hq : ∀i∈nativeLowIndexFinset,ContDiff ℝ 2 (q i)) :
    nativeCollarNormalTraceCLM (nativeBubbleLowCollarJet t₀ q hq)=
      nativeAngularTraceCLM (-deriv (bubbleLowAngularCurve q) t₀-(1/2:ℝ) • bubbleLowAngularCurve q t₀) := by
  unfold nativeBubbleLowCollarJet
  rw [nativeFiniteCollarJet_normal_trace,(bubbleLowAngularCurve_hasDerivAt q hq t₀).deriv]
  congr 1
  have hd (i : AngularIndex) (hi : i∈nativeLowIndexFinset) :
      deriv (fun t => q i (t₀+t)) 0=deriv (q i) t₀ := by
    have h := ((hq i hi).differentiable (by norm_num) t₀).hasDerivAt
    have h' : HasDerivAt (q i) (deriv (q i) t₀) (t₀+0) := by simpa only [add_zero] using h
    exact (h'.comp_const_add t₀ 0).deriv
  have he : (∑i∈nativeLowIndexFinset,(deriv (fun t => q i (t₀+t)) 0+q i (t₀+0)/2) • angularBasis i)=
      (∑i∈nativeLowIndexFinset,deriv (q i) t₀ • angularBasis i)+(1/2:ℝ) • bubbleLowAngularCurve q t₀ := by
    rw [bubbleLowAngularCurve,Finset.smul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hd i hi,add_zero,add_smul,smul_smul]
    congr 2
    ring
  rw [he,neg_add,sub_eq_add_neg]

#print axioms nativeBubbleLowCollarJet_value_trace
#print axioms nativeBubbleLowCollarJet_normal_trace
end Yamabe3.Analysis.SpherePolar
