import Yamabe3.Analysis.NativeH4MatchedGlobalSource
import Yamabe3.Analysis.NativeH4MatchedCollar
import Yamabe3.Analysis.NativeSupportedGlobalFeedback

/-! The actual residual of the original matched H4 field drives the
existing two-sided L2 solver. The original source itself is not inserted
in that space. One bounded linear correction satisfies the full fixed
point equation and preserves the outer support required by the producer. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  {τ : ℝ} (ht : 0<τ)

def nativeH4MatchedExteriorErrorCLM (g : RiemannianMetric 3 E) (ε : ℝ) :
    HalfEndPhysicalH4Graph →L[ℝ] NativeCollarL2 :=
  (nativeBCFCollarErrorCLM g ε (nativePoissonExteriorPotential (fullBubbleHighPotential (-τ)))).comp
    (nativeCollarJetClosure.subtypeL.comp (nativeH4MatchedExteriorJetCLM P ht))

def nativeH4MatchedGlobalResidualCLM (g : RiemannianMetric 3 E) (ε : ℝ) :
    HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource :=
  (nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp g ε).prod
    (nativeFullCollarSourceReturnCLM.comp (nativeH4MatchedExteriorErrorCLM P ht g ε))

theorem exists_nativeH4MatchedGlobalResidual_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃C : ℝ,0<C ∧ ∀ε : ℝ,0≤ε → ε≤1 → ∀a∈Λ,
      ‖nativeH4MatchedGlobalResidualCLM P hp ht (g a) ε‖≤C*ε := by
  obtain ⟨H,hH,hh⟩ := exists_nativeH4MatchedInnerGlobalSource_bound (fullBubbleHighPotential (-τ)) P hp Λ g hB hρ
  let V := nativePoissonExteriorPotential (fullBubbleHighPotential (-τ))
  obtain ⟨C,hC,hc⟩ := exists_native_bcf_full_collar_error_linear_bound Λ g hB hρ (norm_nonneg V)
  let K := nativeH4MatchedExteriorJetCLM P ht
  let A := nativeFullCollarSourceReturnCLM
  let D := H+1+‖A‖*C*‖K‖
  have hD : 0<D := by dsimp only [D];positivity
  refine ⟨D,hD,fun ε hε hε1 a ha => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)⟩
  have hi := (nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε).le_of_opNorm_le
    (hh ε hε hε1 a ha) v
  have he := hc ε hε hε1 a ha V le_rfl (K v).val
  change ‖nativeH4MatchedExteriorErrorCLM P ht (g a) ε v‖≤C*ε*‖K v‖ at he
  have ho := A.le_opNorm (nativeH4MatchedExteriorErrorCLM P ht (g a) ε v)
  have hbnd : ‖A (nativeH4MatchedExteriorErrorCLM P ht (g a) ε v)‖≤(‖A‖*C*‖K‖)*ε*‖v‖ := by
    apply ho.trans
    apply (mul_le_mul_of_nonneg_left he (norm_nonneg A)).trans
    have hh := mul_le_mul_of_nonneg_left (K.le_opNorm v) (by positivity : 0≤‖A‖*(C*ε))
    nlinarith only [hh]
  change ‖(nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε v,
    A (nativeH4MatchedExteriorErrorCLM P ht (g a) ε v))‖≤_
  rw [Prod.norm_def]
  apply max_le
  · exact hi.trans (by
      dsimp only [D]
      nlinarith [mul_nonneg hε (norm_nonneg v),
        mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg A) hC.le) (norm_nonneg K)) (mul_nonneg hε (norm_nonneg v))])
  · exact hbnd.trans (by
      dsimp only [D]
      nlinarith [mul_nonneg hε (norm_nonneg v),
        mul_nonneg hH.le (mul_nonneg hε (norm_nonneg v))])

variable (v₀ : ℝ→ℝ) (hv : Continuous v₀) (hb : ∀t,0≤v₀ t ∧ v₀ t≤1) (b : ℝ)

theorem exists_nativeH4Matched_residual_correction
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃ε₀ C : ℝ,0<ε₀ ∧ ε₀≤1 ∧ 0<C ∧ ∀ε : ℝ,0≤ε → ε≤ε₀ → ∀a∈Λ,
      ∃T : HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource,
        ‖T‖≤C*ε ∧ ∀v,T v=nativeH4MatchedGlobalResidualCLM P hp ht (g a) ε v+
          nativeSupportedTwoSidedGlobalSourceCLM P hp v₀ hv hb b ht (g a) ε (T v) := by
  obtain ⟨ε₀,hε₀,hε₁,hs⟩ := exists_nativeSupportedTwoSidedGlobal_feedback P hp v₀ hv hb b ht Λ g hB hρ
  obtain ⟨C,hC,hc⟩ := exists_nativeH4MatchedGlobalResidual_bound P hp ht Λ g hB hρ
  refine ⟨ε₀,2*C,hε₀,hε₁,by positivity,fun ε hε hε0 a ha => ?_⟩
  obtain ⟨S,hS,hfix⟩ := hs ε hε hε0 a ha
  let R := nativeH4MatchedGlobalResidualCLM P hp ht (g a) ε
  refine ⟨S.comp R,?_,fun v => hfix (R v)⟩
  apply (ContinuousLinearMap.opNorm_comp_le S R).trans
  have hh := mul_le_mul hS (hc ε hε (hε0.trans hε₁) a ha) (norm_nonneg R) (by norm_num : (0:ℝ)≤2)
  exact hh.trans_eq (by ring)

theorem nativeH4Matched_correction_outer_support
    (g : RiemannianMetric 3 E) (ε : ℝ) (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource)
    (hY : Y=nativeH4MatchedGlobalResidualCLM P hp ht g ε x+
      nativeSupportedTwoSidedGlobalSourceCLM P hp v₀ hv hb b ht g ε Y)
    (hb0 : b≤ -(1/2:ℝ)) : ∀ᵐt : ℝ ∂volume,t<b → Y.2 t=0 := by
  apply nativeSupportedTwoSidedGlobal_outer_source_lower_support P hp v₀ hv hb b ht g ε _ Y hY hb0
  have hs := nativeFullCollarSourceReturn_time_support (nativeH4MatchedExteriorErrorCLM P ht g ε x)
  filter_upwards [hs] with t ht'
  intro htb
  apply ht'
  intro hc
  linarith [hc.1]

#print axioms exists_nativeH4MatchedGlobalResidual_bound
#print axioms exists_nativeH4Matched_residual_correction
#print axioms nativeH4Matched_correction_outer_support
end Yamabe3.Analysis.UniformElliptic
