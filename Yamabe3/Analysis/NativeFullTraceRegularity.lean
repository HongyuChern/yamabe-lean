import Yamabe3.Analysis.NativeLowTraceRegularity

/-! Full high/low same-source fields carry genuine three-halves value
and half-order normal traces, with constants before the potential family. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (P : NativeHighPotential)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1)

def nativeFullL2NormalAngularCLM : Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] AngularL2 :=
  nativeTraceAngularCLM.comp (nativeCollarNormalTraceCLM.comp (nativeFullL2AllScaleJetCLM P hp v hv hb 0))

theorem nativeFullL2NormalAngular_eq
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    nativeFullL2NormalAngularCLM P hp v hv hb F=
      nativeL2HalfNormalAngularCLM P hp F+nativeLowL2NormalAngularCLM v hv hb F := by
  change nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeFullL2AllScaleJetCLM P hp v hv hb 0 F))=_
  rw [nativeFullL2_normal_trace,map_add,nativeTraceAngular_left_inverse]
  rfl

theorem nativeFullL2NormalAngular_half_bound
    (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    NativeAngularSpectralRegular (1/2) (nativeFullL2NormalAngularCLM P hp v hv hb F) ∧
      (∑' i,nativeAngularWeightedSquare (1/2) (nativeFullL2NormalAngularCLM P hp v hv hb F) i)≤
        (2*(3+4*P.derivativeBound^2)*(50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2+
          7744*(eLpNorm (futureL2Kernel 2) 2).toReal^2)*‖F‖^2 := by
  obtain ⟨hh,hhb⟩ := nativeL2HalfNormalAngular_half_bound P hp F
  have hl := nativeLowL2_true_trace_spectral_bounds v hv hb F
  obtain ⟨hn,hnb⟩ := nativeAngularSpectralRegular_smul hl.2.1 (-1)
  simp only [neg_one_smul] at hn hnb
  obtain ⟨hs,hsb⟩ := nativeAngularSpectralRegular_sub hh hn
  simp only [sub_neg_eq_add] at hs hsb
  rw [nativeFullL2NormalAngular_eq]
  refine ⟨hs,?_⟩
  norm_num at hnb
  nlinarith only [hhb,hl.2.2.2,hnb,hsb]

omit P hp v hv hb in
theorem exists_family_nativeFullL2_trace_spectral_bounds {κ M : ℝ}
    (hκ0 : 0≤κ) (hκ1 : κ<1) (hM : 0≤M) :
    ∃ C : ℝ,0≤C ∧ ∀ (P : NativeHighPotential),P.κ=κ → ‖P.potential‖≤M →
      ∀ (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
        (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0≤v t ∧ v t≤1)
        (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)),
        NativeAngularSpectralRegular (3/2) (nativeTraceAngularCLM
          (nativeCollarValueTraceCLM (nativeFullL2AllScaleJetCLM P hp v hv hb 0 F))) ∧
        NativeAngularSpectralRegular (1/2) (nativeFullL2NormalAngularCLM P hp v hv hb F) ∧
        (∑' i,nativeAngularWeightedSquare (3/2) (nativeTraceAngularCLM
          (nativeCollarValueTraceCLM (nativeFullL2AllScaleJetCLM P hp v hv hb 0 F))) i)+
        (∑' i,nativeAngularWeightedSquare (1/2) (nativeFullL2NormalAngularCLM P hp v hv hb F) i)≤C*‖F‖^2 := by
  let D := 1+(10/9:ℝ)*M/(1-κ)
  let B := 1+M*((1-κ)⁻¹*(4/9))
  let K := (eLpNorm (futureL2Kernel 2) 2).toReal
  refine ⟨2*(3+4*D^2)*(50/9)*B^2+7872*K^2,by positivity,?_⟩
  intro P hP hPM hp v hv hb F
  have hD : P.derivativeBound≤D := by
    unfold NativeHighPotential.derivativeBound
    dsimp only [D]
    rw [hP]
    gcongr
  have hD0 : 0≤P.derivativeBound := P.derivativeBound_nonneg
  have hB : 1+‖P.potential‖*((1-P.κ)⁻¹*(4/9))≤B := by
    dsimp only [B]
    rw [hP]
    gcongr
  have hB0 : 0≤1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)) := by
    have hκ := P.κ_lt_one
    positivity
  have hl := nativeLowL2_true_trace_spectral_bounds v hv hb F
  have hn := nativeFullL2NormalAngular_half_bound P hp v hv hb F
  rw [nativeFullL2_value_trace,nativeTraceAngular_left_inverse]
  refine ⟨hl.1,hn.1,?_⟩
  have he : 2*(3+4*P.derivativeBound^2)*(50/9)*(1+‖P.potential‖*((1-P.κ)⁻¹*(4/9)))^2≤
      2*(3+4*D^2)*(50/9)*B^2 := by gcongr
  have heF := mul_le_mul_of_nonneg_right he (sq_nonneg ‖F‖)
  dsimp only [K]
  nlinarith only [hl.2.2.1,hn.2,heF]

#print axioms nativeFullL2NormalAngular_eq
#print axioms nativeFullL2NormalAngular_half_bound
#print axioms exists_family_nativeFullL2_trace_spectral_bounds
end Yamabe3.Analysis.SpherePolar
