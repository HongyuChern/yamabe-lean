import Yamabe3.Analysis.SpectralL2LowerSupportDecay
import Yamabe3.Analysis.SpectralL2PotentialContinuous

/-! Two exponential bootstraps for the same weighted L2 inverse.
The source may be arbitrary L2 above a fixed lower time bound. The
potential's genuine exp(2t) tail, rather than boundedness alone, pays
for decay after the exp(-2t) conjugation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Filter MeasureTheory
open scoped Topology ENNReal lp BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay

theorem spectralL2PotentialContinuous_split {ι : Type*} (k : ι→ℝ) {k₀ δ : ℝ}
    (hk₀ : 0<k₀) (hk : ∀i,k₀≤k i) (hδ : |δ|<k₀) (V : ℝ→ᵇℝ)
    (F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ)) (t : ℝ) :
    spectralL2PotentialContinuousCLM k hk₀ hk hδ V F t=
      spectralL2Convolution k hk₀ hk δ F t-
      spectralL2Convolution k hk₀ hk δ
        (spectralL2PotentialMulCLM V (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)) t := by
  change spectralL2SmoothingCLM k hk₀ hk hδ
    (F-spectralL2PotentialMulCLM V (spectralL2IntegralPotentialInverse k hk₀ hk hδ V F)) t=_
  rw [map_sub]
  rfl

theorem exists_spectralL2Potential_far_end_decay {ι : Type*} (k : ι→ℝ)
    (hk : ∀i,(5/2:ℝ)≤k i) {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (V : ℝ→ᵇℝ)
    (hm : ∀t,(∫s : ℝ,spectralMajorant (5/2) (-2) s*|V (t-s)|)≤κ)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|V (t-s)|)≤κ)
    (C : ℝ) (hC : 0≤C) (hV : ∀t,|V t|≤C*Real.exp (2*t)) (b : ℝ) :
    ∃D : ℝ,0≤D ∧ ∀F : Lp (SpectralSpace ι) 2 (volume : Measure ℝ),
      (∀ᵐs : ℝ ∂volume,s<b → F s=0) → ∀t : ℝ,
      ‖spectralL2PotentialContinuousCLM k (by norm_num : (0:ℝ)<5/2) hk
        (by norm_num : |(-2:ℝ)|<5/2) V F t‖≤D*‖F‖*Real.exp (4*t) := by
  obtain ⟨C₂,hC₂,h₂⟩ := exists_spectralL2_lower_support_decay k
    (by norm_num : (0:ℝ)<5/2) hk (by norm_num : |(-2:ℝ)|<5/2)
    (by norm_num : (0:ℝ)<2) (by norm_num : |(-2:ℝ)+2|≤5/2) b
  obtain ⟨C₄,hC₄,h₄⟩ := exists_spectralL2_lower_support_decay k
    (by norm_num : (0:ℝ)<5/2) hk (by norm_num : |(-2:ℝ)|<5/2)
    (by norm_num : (0:ℝ)<4) (by norm_num : |(-2:ℝ)+4|≤5/2) b
  let S := spectralL2PotentialContinuousCLM k (by norm_num : (0:ℝ)<5/2) hk
    (by norm_num : |(-2:ℝ)|<5/2) V
  let B := C₂+C*‖S‖/(25/4)
  let D := C₄+C*B/(9/4)
  have hB : 0≤B := by dsimp only [B];positivity
  have hD : 0≤D := by dsimp only [D];positivity
  refine ⟨D,hD,fun F hF t => ?_⟩
  let U := S F
  let M := spectralL2PotentialMulCLM V (spectralL2IntegralPotentialInverse k
    (by norm_num : (0:ℝ)<5/2) hk (by norm_num : |(-2:ℝ)|<5/2) V F)
  have hMae : (M : ℝ→SpectralSpace ι)=ᵐ[volume](fun s => V s • U s) := by
    have ha := spectralL2PotentialContinuous_coe_ae k (by norm_num : (0:ℝ)<5/2) hk
      (by norm_num : |(-2:ℝ)|<5/2) hκ0 hκ1 V hm (by simpa using hp) F
    filter_upwards [spectralL2PotentialMul_coe_ae V
      (spectralL2IntegralPotentialInverse k (by norm_num : (0:ℝ)<5/2) hk
        (by norm_num : |(-2:ℝ)|<5/2) V F),ha] with s hs hu
    change M s=V s • U s
    exact hs.trans (congrArg (fun z => V s • z) hu.symm)
  have hsplit (s : ℝ) : U s=spectralL2Convolution k (by norm_num : (0:ℝ)<5/2) hk (-2) F s-
      spectralL2Convolution k (by norm_num : (0:ℝ)<5/2) hk (-2) M s :=
    spectralL2PotentialContinuous_split k _ hk _ V F s
  have hU0 (s : ℝ) : ‖U s‖≤‖S‖*‖F‖ := (U.norm_coe_le_norm s).trans (S.le_opNorm F)
  have hM2 : ∀ᵐs : ℝ ∂volume,‖M s‖≤(C*‖S‖*‖F‖)*Real.exp (2*s) := by
    filter_upwards [hMae] with s hs
    rw [hs,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hV s) (hU0 s) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hU2 (s : ℝ) : ‖U s‖≤B*‖F‖*Real.exp (2*s) := by
    have hm₂ := spectralL2Convolution_exp_bound k (by norm_num : (0:ℝ)<5/2) hk
      (by norm_num : |(-2:ℝ)|<5/2) (by norm_num : |(-2:ℝ)+2|<5/2) M (Lp.memLp M) hM2 s
    norm_num only at hm₂
    rw [hsplit]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (h₂ F hF s) hm₂).trans_eq
    dsimp only [B]
    norm_num
    ring
  have hM4 : ∀ᵐs : ℝ ∂volume,‖M s‖≤(C*B*‖F‖)*Real.exp (4*s) := by
    filter_upwards [hMae] with s hs
    rw [hs,norm_smul,Real.norm_eq_abs]
    apply (mul_le_mul (hV s) (hU2 s) (norm_nonneg _) (by positivity)).trans_eq
    calc
      _ = C*B*‖F‖*(Real.exp (2*s)*Real.exp (2*s)) := by ring
      _ = _ := by rw [←Real.exp_add];congr 2;ring
  have hm₄ := spectralL2Convolution_exp_bound k (by norm_num : (0:ℝ)<5/2) hk
    (by norm_num : |(-2:ℝ)|<5/2) (by norm_num : |(-2:ℝ)+4|<5/2) M (Lp.memLp M) hM4 t
  change ‖U t‖≤_
  rw [hsplit]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (h₄ F hF t) hm₄).trans_eq
  dsimp only [D]
  norm_num
  ring

#print axioms spectralL2PotentialContinuous_split
#print axioms exists_spectralL2Potential_far_end_decay
end Yamabe3.Analysis.Delaunay
