import Yamabe3.Analysis.NativeLowCauchyBoundedCollar

/-! The bounded low producer retains the same real equation, both
entrance data and decay. Its sphere traces are the actual C2 traces. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeLowCauchyQ_spec {t₀ : ℝ} (ht : 0<t₀) (d n : AngularL2)
    (i : AngularIndex) (hi : i∈nativeLowIndexFinset) :
    let q := nativeLowCauchyQ ht (nativeLowCauchyCoordinateCLM (d,n)) i
    ContDiff ℝ 2 q ∧
      (∀t,deriv (deriv q) t-bubbleLowCoefficient i t*q t=
        -bubbleLowCauchyCompensation i t₀ (inner ℝ (angularBasis i) d)
          (inner ℝ (angularBasis i) n) 0*bubbleCompensation i t) ∧
      q t₀=inner ℝ (angularBasis i) d ∧ deriv q t₀=inner ℝ (angularBasis i) n ∧
      Tendsto q atBot (𝓝 0) ∧ Tendsto (deriv q) atBot (𝓝 0) := by
  dsimp only
  rw [nativeLowCauchyQ,dif_pos hi]
  exact bubbleLowZeroCauchyLinear_spec i hi ht _ _

theorem nativeLowCauchyQ_angular_entrance {t₀ : ℝ} (ht : 0<t₀) (d n : AngularL2) :
    let q := nativeLowCauchyQ ht (nativeLowCauchyCoordinateCLM (d,n))
    bubbleLowAngularCurve q t₀=nativeLowProjection d ∧
      HasDerivAt (bubbleLowAngularCurve q) (nativeLowProjection n) t₀ := by
  dsimp only
  let q := nativeLowCauchyQ ht (nativeLowCauchyCoordinateCLM (d,n))
  have hv : bubbleLowAngularCurve q t₀=nativeLowProjection d := by
    rw [bubbleLowAngularCurve,nativeLowProjection_eq_finite]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [q]
    rw [(nativeLowCauchyQ_spec ht d n i hi).2.2.1]
  refine ⟨hv,?_⟩
  have hn : (∑i∈nativeLowIndexFinset,deriv (q i) t₀ • angularBasis i)=nativeLowProjection n := by
    rw [nativeLowProjection_eq_finite]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [q]
    rw [(nativeLowCauchyQ_spec ht d n i hi).2.2.2.1]
  exact (bubbleLowAngularCurve_hasDerivAt q (nativeLowCauchyQ_C2 ht _) t₀).congr_deriv hn

theorem nativeLowCauchyCollarCLM_traces {t₀ : ℝ} (ht : 0<t₀) (d n : AngularL2) :
    nativeCollarValueTraceCLM (nativeLowCauchyCollarCLM ht (d,n))=
      nativeAngularTraceCLM (nativeLowProjection d) ∧
    nativeCollarNormalTraceCLM (nativeLowCauchyCollarCLM ht (d,n))=
      nativeAngularTraceCLM (-nativeLowProjection n-(1/2:ℝ) • nativeLowProjection d) := by
  rw [nativeLowCauchyCollarCLM_eq,nativeBubbleLowCollarJet_value_trace,
    nativeBubbleLowCollarJet_normal_trace,(nativeLowCauchyQ_angular_entrance ht d n).1,
    (nativeLowCauchyQ_angular_entrance ht d n).2.deriv]
  exact ⟨rfl,rfl⟩

#print axioms nativeLowCauchyQ_spec
#print axioms nativeLowCauchyQ_angular_entrance
#print axioms nativeLowCauchyCollarCLM_traces
end Yamabe3.Analysis.SpherePolar
