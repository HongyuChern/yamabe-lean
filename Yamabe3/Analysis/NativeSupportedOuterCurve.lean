import Yamabe3.Analysis.NativeLowCauchyAngularBound
import Yamabe3.Analysis.NativeSupportedOuterSameField
import Yamabe3.Analysis.NativeBubbleFullSupportedDecay
import Yamabe3.Analysis.NativeExteriorHighFarEnd

/-! The complete supported outer field includes high particular, low
particular, computed low Cauchy correction and the same high boundary
correction. Its decay is attached to one angular curve and all its jets. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

def nativeSupportedOuterCurve (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2) (σ:AngularH1) (t:ℝ) : AngularL2 :=
  nativeBubbleFullSupportedCurve τ b F t+
    nativeLowCauchyCurve ht (nativeLowCauchyCoordinateCLM
      (nativeBubbleLowCorrectionDataCLM τ (nativeSupportedReverseSourcePrepareCLM b F,(d,n)))) t-
    nativePoissonExteriorCurve (fullBubbleHighPotential (-τ))
      (nativeL2EntranceH1CLM (fullBubbleHighPotential τ).κ_nonneg (fullBubbleHighPotential τ).κ_lt_one
        (fullBubblePhasePotential τ) (fullBubbleHighPotential τ).kernel_bound (fullBubblePhasePotential_plus_kernel τ) F) t+
    nativePoissonExteriorCurve (fullBubbleHighPotential (-τ)) σ t

theorem exists_nativeSupportedOuterCurve_halfLine_bound (b:ℝ) {τ:ℝ} (ht:0<τ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2) (σ:AngularH1),
      (∀ᵐs:ℝ ∂volume,s<b→F s=0)→∀t:ℝ,t≤0→
      ‖nativeSupportedOuterCurve b ht F d n σ t‖≤C*(‖(F,(d,n))‖+‖σ‖) := by
  obtain ⟨D,hD,hd⟩:=exists_nativeBubbleFullSupported_decay_bound τ b
  obtain ⟨L,hL,hl⟩:=exists_nativeLowCauchyCurve_halfLine_bound ht 0
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
  have he:Real.exp (2*t)≤1:=Real.exp_le_one_iff.mpr (by linarith only [ht'])
  have hp:‖nativeBubbleFullSupportedCurve τ b F t‖≤D*‖X‖:=
    ((hd F hF t).1.trans (mul_le_of_le_one_right (mul_nonneg hD (norm_nonneg _)) he)).trans
      (mul_le_mul_of_nonneg_left hFn hD)
  have hc:‖nativeLowCauchyCurve ht (T X) t‖≤(L*‖T‖)*‖X‖:=
    (hl (T X) t ht').trans ((mul_le_mul_of_nonneg_left (T.le_opNorm X) hL).trans_eq (by ring))
  have ha:‖nativePoissonExteriorCurve B (A F) t‖≤(‖A‖/(1-B.κ))*‖X‖:=by
    apply ((nativePoissonExteriorCurve_far_end_bound B (A F) t ht').trans
      (mul_le_of_le_one_right (div_nonneg (norm_nonneg _) hk.le) he)).trans
    have h:=div_le_div_of_nonneg_right ((A.le_opNorm F).trans
      (mul_le_mul_of_nonneg_left hFn (norm_nonneg _))) hk.le
    exact h.trans_eq (by ring)
  have hs:‖nativePoissonExteriorCurve B σ t‖≤(1/(1-B.κ))*‖σ‖:=by
    exact ((nativePoissonExteriorCurve_far_end_bound B σ t ht').trans
      (mul_le_of_le_one_right (div_nonneg (norm_nonneg _) hk.le) he)).trans_eq (by ring)
  change ‖nativeBubbleFullSupportedCurve τ b F t+nativeLowCauchyCurve ht (T X) t-
    nativePoissonExteriorCurve B (A F) t+nativePoissonExteriorCurve B σ t‖≤_
  have hn:=norm_add_le (nativeBubbleFullSupportedCurve τ b F t+nativeLowCauchyCurve ht (T X) t-
    nativePoissonExteriorCurve B (A F) t) (nativePoissonExteriorCurve B σ t)
  have hn2:=norm_sub_le (nativeBubbleFullSupportedCurve τ b F t+nativeLowCauchyCurve ht (T X) t)
    (nativePoissonExteriorCurve B (A F) t)
  have hn3:=norm_add_le (nativeBubbleFullSupportedCurve τ b F t) (nativeLowCauchyCurve ht (T X) t)
  change _≤C*(‖X‖+‖σ‖)
  dsimp only [C]
  have hnX:=norm_nonneg X
  have hnσ:=norm_nonneg σ
  have hLnorm:0≤L*‖T‖:=mul_nonneg hL (norm_nonneg _)
  have hAnorm:0≤‖A‖/(1-B.κ):=div_nonneg (norm_nonneg A) hk.le
  have hInv:0≤1/(1-B.κ):=by positivity
  nlinarith only [hn,hn2,hn3,hp,hc,ha,hs,mul_nonneg hD hnσ,mul_nonneg hLnorm hnσ,
    mul_nonneg hAnorm hnσ,mul_nonneg hInv hnX]

theorem nativeSupportedOuterCurve_physical_decay (b:ℝ) {τ:ℝ} (ht:0<τ)
    (F:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (d n:AngularL2) (σ:AngularH1)
    (hF:∀ᵐs:ℝ ∂volume,s<b→F s=0) :
    Tendsto (fun t:ℝ=>Real.exp (t/2) • nativeSupportedOuterCurve b ht F d n σ t) atBot (𝓝 0) := by
  obtain ⟨C,hC,h⟩:=exists_nativeSupportedOuterCurve_halfLine_bound b ht
  have hb:∀ᶠt in atBot,‖Real.exp (t/2) • nativeSupportedOuterCurve b ht F d n σ t‖≤
      C*(‖(F,(d,n))‖+‖σ‖)*Real.exp (t/2):=by
    filter_upwards [eventually_le_atBot (0:ℝ)] with t ht'
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left (h F d n σ hF t ht') (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  apply squeeze_zero_norm' hb
  simpa using (Real.tendsto_exp_atBot.comp (tendsto_id.atBot_div_const (by norm_num : (0:ℝ)<2))).const_mul
    (C*(‖(F,(d,n))‖+‖σ‖))

#print axioms exists_nativeSupportedOuterCurve_halfLine_bound
#print axioms nativeSupportedOuterCurve_physical_decay
end Yamabe3.Analysis.SpherePolar
