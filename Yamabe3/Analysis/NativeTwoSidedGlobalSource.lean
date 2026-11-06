import Yamabe3.Analysis.NativeTwoSidedAllScale
import Yamabe3.Analysis.NativeMatchedGeometricSource

/-! Norm-convergent full-mode geometric feedback on the whole inner
half-end and the actual outer collar, both driven by one pair of sources.
No low residual is projected away. Bounds here fix the model first. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (P : NativeHighPotential)
  (hp : ∀ t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1) (t₀ : ℝ)

def nativeTwoSidedGeometricRowCLM (g : RiemannianMetric 3 E) (ε s : ℝ) :
    NativeTwoSidedSource →L[ℝ] NativeCollarL2 :=
  (nativeBCFCollarErrorCLM g (ε*Real.exp (-s)) (boundedTimeTranslate ℝ s P.potential)).comp
    (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s)

def nativeTwoSidedGeometricSourceTerm (g : RiemannianMetric 3 E) (ε : ℝ) (n : ℕ) :
    NativeTwoSidedSource →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)).comp
    (nativeTwoSidedGeometricRowCLM P hp v hv hb t₀ g ε (nativeLogShellCenter n))

def nativeTwoSidedInnerGlobalSourceCLM (g : RiemannianMetric 3 E) (ε : ℝ) :
    NativeTwoSidedSource →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  ∑'n,nativeTwoSidedGeometricSourceTerm P hp v hv hb t₀ g ε n

theorem exists_nativeTwoSidedGeometricRow_decay
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0≤ε → ε≤1 → ∀ a ∈ Λ, ∀ s : ℝ,0 ≤ s →
      ‖nativeTwoSidedGeometricRowCLM P hp v hv hb t₀ (g a) ε s‖≤C*ε*Real.exp (-s) := by
  obtain ⟨C,hC,hc⟩ := exists_native_bcf_full_collar_error_linear_bound Λ g hB hρ (norm_nonneg P.potential)
  obtain ⟨D,hD,hd⟩ := exists_nativeTwoSidedAllScale_bound P hp v hv hb t₀
  refine ⟨C*D,by positivity,fun ε hε hε1 a ha s hs => ?_⟩
  have he : Real.exp (-s)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro X
  have h := hc (ε*Real.exp (-s)) (by positivity) ((mul_le_of_le_one_right hε he).trans hε1)
    a ha (boundedTimeTranslate ℝ s P.potential) (boundedTimeTranslate_norm ℝ s P.potential).le
    (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X)
  have hj := (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s).le_of_opNorm_le (hd s) X
  exact (h.trans (mul_le_mul_of_nonneg_left hj (by positivity))).trans_eq (by ring)

theorem exists_nativeTwoSidedGeometricSourceTerm_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0≤ε → ε≤1 → ∀ a ∈ Λ, ∀ n : ℕ,
      ‖nativeTwoSidedGeometricSourceTerm P hp v hv hb t₀ (g a) ε n‖≤C*ε*Real.exp (-nativeLogShellCenter n) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeTwoSidedGeometricRow_decay P hp v hv hb t₀ Λ g hB hρ
  let L := ‖nativeL2FullPhysicalSourceCLM‖*Real.exp 1
  have hL : 0≤L := by positivity
  refine ⟨(L+1)*C,by positivity,fun ε hε hε1 a ha n => ?_⟩
  have ht := ContinuousLinearMap.opNorm_comp_le (nativeFullShellSourceReturnCLM (nativeLogShellCenter n))
    (nativeTwoSidedGeometricRowCLM P hp v hv hb t₀ (g a) ε (nativeLogShellCenter n))
  have hr := hc ε hε hε1 a ha (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n)
  apply ht.trans
  apply (mul_le_mul (nativeFullShellSourceReturn_norm (nativeLogShellCenter n)) hr (norm_nonneg _) hL).trans
  change L*(C*ε*Real.exp (-nativeLogShellCenter n))≤_
  nlinarith [Real.exp_pos (-nativeLogShellCenter n),mul_nonneg hC.le hε]

theorem nativeTwoSidedGeometricSourceTerm_summable
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ) :
    Summable (nativeTwoSidedGeometricSourceTerm P hp v hv hb t₀ (g a) ε) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeTwoSidedGeometricSourceTerm_bound P hp v hv hb t₀ Λ g hB hρ
  exact (nativeLogShell_decay_summable.mul_left (C*ε)).of_norm_bounded (hc ε hε hε1 a ha)

theorem exists_nativeTwoSidedInnerGlobalSource_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0≤ε → ε≤1 → ∀ a ∈ Λ, 
      ‖nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb t₀ (g a) ε‖≤C*ε := by
  obtain ⟨C,hC,hc⟩ := exists_nativeTwoSidedGeometricSourceTerm_bound P hp v hv hb t₀ Λ g hB hρ
  let S := Real.exp (-(1/4:ℝ))*(1-Real.exp (-(1/2:ℝ)))⁻¹
  have hS : 0<S := by
    dsimp only [S]
    exact mul_pos (Real.exp_pos _) (inv_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))))
  refine ⟨C*S,by positivity,fun ε hε hε1 a ha => ?_⟩
  have h := tsum_of_norm_bounded ((nativeLogShell_decay_summable.hasSum).mul_left (C*ε)) (hc ε hε hε1 a ha)
  rw [nativeLogShell_decay_sum] at h
  exact h.trans_eq (by dsimp only [S];ring)

variable {t₀} (ht : 0<t₀)

def nativeTwoSidedGlobalSourceCLM (g : RiemannianMetric 3 E) (ε : ℝ) :
    NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource :=
  (nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb t₀ g ε).prod
    (nativeFullCollarSourceReturnCLM.comp (nativeTwoSidedExteriorErrorCLM P hp v hv hb ht g ε))

theorem exists_nativeTwoSidedGlobalSource_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0≤ε → ε≤1 → ∀ a ∈ Λ, 
      ‖nativeTwoSidedGlobalSourceCLM P hp v hv hb ht (g a) ε‖≤C*ε := by
  obtain ⟨C,hC,hc⟩ := exists_nativeTwoSidedInnerGlobalSource_bound P hp v hv hb t₀ Λ g hB hρ
  obtain ⟨D,hD,hd⟩ := exists_nativeTwoSidedCollarSourceError_linear_bound P hp v hv hb ht Λ g hB hρ
  refine ⟨C+D,by positivity,fun ε hε hε1 a ha => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro X
  have hi := (nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb t₀ (g a) ε).le_of_opNorm_le (hc ε hε hε1 a ha) X
  have ho := (norm_snd_le (nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht (g a) ε X)).trans
    ((nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht (g a) ε).le_of_opNorm_le (hd ε hε hε1 a ha) X)
  change ‖(nativeTwoSidedInnerGlobalSourceCLM P hp v hv hb t₀ (g a) ε X,
    nativeFullCollarSourceReturnCLM (nativeTwoSidedExteriorErrorCLM P hp v hv hb ht (g a) ε X))‖≤_
  rw [Prod.norm_def]
  apply max_le
  · exact hi.trans (by nlinarith [mul_nonneg (mul_nonneg hD.le hε) (norm_nonneg X)])
  · exact ho.trans (by nlinarith [mul_nonneg (mul_nonneg hC.le hε) (norm_nonneg X)])

#print axioms exists_nativeTwoSidedGeometricRow_decay
#print axioms exists_nativeTwoSidedGeometricSourceTerm_bound
#print axioms nativeTwoSidedGeometricSourceTerm_summable
#print axioms exists_nativeTwoSidedInnerGlobalSource_bound
#print axioms exists_nativeTwoSidedGlobalSource_bound
end Yamabe3.Analysis.SpherePolar
