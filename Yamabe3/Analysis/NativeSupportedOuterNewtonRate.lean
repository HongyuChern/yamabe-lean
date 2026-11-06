import Yamabe3.Analysis.BubbleLowCauchyFarRate
import Yamabe3.Analysis.NativeSupportedOuterCurve

/-! Actual Newton-rate far decay of the complete supported outer curve,
including the same computed low compensation and both high boundary terms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem exists_nativeLowCauchyCurve_far_rate {τ:ℝ} (ht:0<τ) :
    ∃C:ℝ,0≤C ∧ ∀(v:NativeLowCauchyCoordinates) (t:ℝ),t≤-τ→‖nativeLowCauchyCurve ht v t‖≤C*‖v‖*Real.exp (t/2) := by
  classical
  let B:AngularIndex→ℝ:=fun i=>if hi:i∈nativeLowIndexFinset then
    (bubbleLowZeroCauchyLinear_far_rate i hi ht).choose else 0
  have hB (i:AngularIndex) (hi:i∈nativeLowIndexFinset):0≤B i:=by
    dsimp only [B];rw [dif_pos hi]
    exact (bubbleLowZeroCauchyLinear_far_rate i hi ht).choose_spec.1
  refine ⟨(∑i∈nativeLowIndexFinset,B i)*Real.exp (τ/2),mul_nonneg (Finset.sum_nonneg hB) (Real.exp_pos _).le,fun v t ht' =>?_⟩
  calc
    ‖nativeLowCauchyCurve ht v t‖ ≤ ∑i∈nativeLowIndexFinset,‖nativeLowCauchyQ ht v i (τ+t) • angularBasis i‖ := norm_sum_le _ _
    _ ≤ ∑i∈nativeLowIndexFinset,(B i*Real.exp (τ/2))*‖v‖*Real.exp (t/2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul,angularBasis.orthonormal.norm_eq_one i,mul_one]
      have hh:=(bubbleLowZeroCauchyLinear_far_rate i hi ht).choose_spec.2
        (v ⟨i,hi⟩).1 (v ⟨i,hi⟩).2 (τ+t) (by linarith only [ht'])
      have hn:max ‖(v ⟨i,hi⟩).1‖ ‖(v ⟨i,hi⟩).2‖≤‖v‖:=by
        simpa only [Prod.norm_def] using norm_le_pi_norm v ⟨i,hi⟩
      change ‖nativeLowCauchyQ ht v i (τ+t)‖≤_
      rw [nativeLowCauchyQ,dif_pos hi]
      apply hh.1.trans
      have hBi:(bubbleLowZeroCauchyLinear_far_rate i hi ht).choose=B i:=by
        dsimp only [B];rw [dif_pos hi]
      rw [hBi]
      have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (hB i hi)) (Real.exp_pos ((τ+t)/2)).le
      apply hh'.trans_eq
      rw [show (τ+t)/2=τ/2+t/2 by ring,Real.exp_add]
      ring
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul]


theorem exists_nativeSupportedOuterCurve_Newton_rate (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2) (σ:AngularH1),
      (∀ᵐs:ℝ ∂volume,s<b→F s=0)→∀t:ℝ,t≤-τ→
      ‖nativeSupportedOuterCurve b ht F d n σ t‖≤C*(‖(F,(d,n))‖+‖σ‖)*Real.exp (t/2) := by
  obtain ⟨D,hD,hd⟩:=exists_nativeBubbleFullSupported_decay_bound τ b
  obtain ⟨L,hL,hl⟩:=exists_nativeLowCauchyCurve_far_rate ht
  let T:=nativeLowCauchyCoordinateCLM.comp ((nativeBubbleLowCorrectionDataCLM τ).comp
    (nativeSupportedLowPhysicalDataCLM b))
  let P:=fullBubbleHighPotential τ
  let B:=fullBubbleHighPotential (-τ)
  let A:=nativeL2EntranceH1CLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound (fullBubblePhasePotential_plus_kernel τ)
  let C:=D+L*‖T‖+‖A‖/(1-B.κ)+1/(1-B.κ)
  have hk:0<1-B.κ:=sub_pos.mpr B.κ_lt_one
  have hC:0≤C:=by dsimp only [C];positivity
  refine ⟨C,hC,fun F d n σ hF t ht' =>?_⟩
  let X:NativeLowInhomogeneousData:=(F,(d,n))
  have hFn:‖F‖≤‖X‖:=norm_fst_le X
  have ht0 : t≤0 := by linarith only [ht',ht]
  have he : Real.exp (2*t)≤Real.exp (t/2) := Real.exp_le_exp.mpr (by linarith only [ht0])
  have hp : ‖nativeBubbleFullSupportedCurve τ b F t‖≤D*‖X‖*Real.exp (t/2) :=
    ((hd F hF t).1.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hD (norm_nonneg _)))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFn hD) (Real.exp_pos _).le)
  have hc : ‖nativeLowCauchyCurve ht (T X) t‖≤(L*‖T‖)*‖X‖*Real.exp (t/2) :=
    (hl (T X) t ht').trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (T.le_opNorm X) hL)
      (Real.exp_pos _).le).trans_eq (by ring))
  have ha : ‖nativePoissonExteriorCurve B (A F) t‖≤(‖A‖/(1-B.κ))*‖X‖*Real.exp (t/2) := by
    apply ((nativePoissonExteriorCurve_far_end_bound B (A F) t ht0).trans
      (mul_le_mul_of_nonneg_left he (div_nonneg (norm_nonneg _) hk.le))).trans
    have h := div_le_div_of_nonneg_right ((A.le_opNorm F).trans
      (mul_le_mul_of_nonneg_left hFn (norm_nonneg _))) hk.le
    exact (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le).trans_eq (by ring)
  have hs : ‖nativePoissonExteriorCurve B σ t‖≤(1/(1-B.κ))*‖σ‖*Real.exp (t/2) := by
    exact ((nativePoissonExteriorCurve_far_end_bound B σ t ht0).trans
      (mul_le_mul_of_nonneg_left he (div_nonneg (norm_nonneg _) hk.le))).trans_eq (by ring)
  change ‖nativeBubbleFullSupportedCurve τ b F t+nativeLowCauchyCurve ht (T X) t-
    nativePoissonExteriorCurve B (A F) t+nativePoissonExteriorCurve B σ t‖≤_
  have hn:=norm_add_le (nativeBubbleFullSupportedCurve τ b F t+nativeLowCauchyCurve ht (T X) t-
    nativePoissonExteriorCurve B (A F) t) (nativePoissonExteriorCurve B σ t)
  have hn2:=norm_sub_le (nativeBubbleFullSupportedCurve τ b F t+nativeLowCauchyCurve ht (T X) t)
    (nativePoissonExteriorCurve B (A F) t)
  have hn3:=norm_add_le (nativeBubbleFullSupportedCurve τ b F t) (nativeLowCauchyCurve ht (T X) t)
  change _≤C*(‖X‖+‖σ‖)*Real.exp (t/2)
  dsimp only [C]
  have hnX:=norm_nonneg X
  have hnσ:=norm_nonneg σ
  have hLnorm:0≤L*‖T‖:=mul_nonneg hL (norm_nonneg _)
  have hAnorm:0≤‖A‖/(1-B.κ):=div_nonneg (norm_nonneg A) hk.le
  have hInv:0≤1/(1-B.κ):=by positivity
  nlinarith only [hn,hn2,hn3,hp,hc,ha,hs,mul_nonneg (mul_nonneg hD hnσ) (Real.exp_pos (t/2)).le,mul_nonneg (mul_nonneg hLnorm hnσ) (Real.exp_pos (t/2)).le,
    mul_nonneg (mul_nonneg hAnorm hnσ) (Real.exp_pos (t/2)).le,mul_nonneg (mul_nonneg hInv hnX) (Real.exp_pos (t/2)).le]

#print axioms exists_nativeLowCauchyCurve_far_rate
#print axioms exists_nativeSupportedOuterCurve_Newton_rate
end Yamabe3.Analysis.SpherePolar
