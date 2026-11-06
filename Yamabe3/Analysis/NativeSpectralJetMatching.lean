import Yamabe3.Analysis.NativeC2BoundarySpectral
import Yamabe3.Analysis.NativeC2C1HighCauchy
import Yamabe3.Analysis.NativeLowCauchyBoundedTraces
import Yamabe3.Analysis.NativeMatchedCollarRegularity

/-! Actual all-mode collar matching for the trace of one given volume
jet. The high datum is the trace of that jet; the coupled inverse and the
finite compensated Cauchy producer are actually applied. No source-space
identification or whole-domain native equation is assumed here. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

private theorem high_idem (f : AngularL2) : nativeHighProjection (nativeHighProjection f)=nativeHighProjection f := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeHighProjection,nativeAngularProjection_coefficient]
  split_ifs <;> rfl

private theorem trace_injective : Function.Injective nativeTraceAngularCLM := by
  intro x y h
  rw [←nativeTraceAngular_right_inverse x,←nativeTraceAngular_right_inverse y,h]

theorem exists_nativeSpectralJet_actual_matching (P : NativeHighPotential) {τ : ℝ} (ht : 0<τ)
    (J : nativeCollarJetClosure)
    (hD : NativeAngularSpectralRegular (3/2) (nativeTraceAngularCLM (nativeCollarValueTraceCLM J)))
    (hN : NativeAngularSpectralRegular (1/2) (nativeTraceAngularCLM (nativeCollarNormalTraceCLM J))) :
    let B := fullBubbleHighPotential (-τ)
    let D := nativeTraceAngularCLM (nativeCollarValueTraceCLM J)
    let N := nativeTraceAngularCLM (nativeCollarNormalTraceCLM J)
    ∃d σ : AngularH1,angularEmbedding d=nativeHighProjection D ∧
      nativeHighEnergyProjectionCLM d=d ∧ nativeHighEnergyProjectionCLM σ=σ ∧
      nativeHighEnergyProjectionCLM (σ+d)=σ+d ∧
      ∃(hd : NativeAngularSpectralRegular (3/2) (angularEmbedding d))
        (hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ))
        (hsd : NativeAngularSpectralRegular (3/2) (angularEmbedding (σ+d))),
      B.dtn (σ+d)+P.dtn σ= -nativeHighProjection N-(1/2:ℝ) • angularEmbedding d ∧
      let Ji := J+nativePoissonCollarJet P σ hσ
      let Ko := nativeLowCauchyCollarCLM ht (D,-N-(1/2:ℝ) • D)+nativePoissonExteriorCollarJet B (σ+d) hsd
      nativeCollarValueTraceCLM Ji=nativeCollarValueTraceCLM Ko ∧
      nativeCollarNormalTraceCLM Ji=nativeCollarNormalTraceCLM Ko ∧
      NativeCollarWeakGluing Ji Ko ∧
      MemWkpLocally 2 (nativeCollarGluedFunction Ji.val.1 Ko.val.1) nativePoissonEntranceCollar := by
  let B := fullBubbleHighPotential (-τ)
  let D := nativeTraceAngularCLM (nativeCollarValueTraceCLM J)
  let N := nativeTraceAngularCLM (nativeCollarNormalTraceCLM J)
  have hDR : NativeAngularSpectralRegular (3/2) (nativeHighProjection D) := (nativeAngularSpectralRegular_high hD).1
  obtain ⟨d,hdD,_⟩ := nativeAngular_three_halves_exists_H1 _ hDR
  have hdR : NativeAngularSpectralRegular (3/2) (angularEmbedding d) := by rwa [hdD]
  have hdh : nativeHighEnergyProjectionCLM d=d := by
    apply angularEmbedding_injective
    rw [nativeHighEnergyProjectionCLM_embedding,hdD,high_idem]
  let n : AngularL2 := -nativeHighProjection N-(1/2:ℝ) • angularEmbedding d
  have hdh' : nativeHighProjection (angularEmbedding d)=angularEmbedding d := by rw [hdD,high_idem]
  have hnh : nativeHighProjection n=n := by rw [map_sub,map_neg,high_idem,map_smul,hdh']
  have hnR : NativeAngularSpectralRegular (1/2) n := by
    exact (nativeAngularSpectralRegular_sub
      (by simpa only [neg_one_smul] using (nativeAngularSpectralRegular_smul (nativeAngularSpectralRegular_high hN).1 (-1)).1)
      (nativeAngularSpectralRegular_smul (nativeAngular_three_halves_to_half _ hdR).1 (1/2)).1).1
  obtain ⟨σ,hσh,hsdh,_,he⟩ := exists_nativeHighCoupled_cauchy_matching B P d hdh n hnh
  have hinv : σ=nativeHighCoupledDtNInverse B P (n-B.dtn d) := by
    have he' : (B.dtn+P.dtn) σ=n-B.dtn d := by
      rw [map_add] at he
      change B.dtn σ+P.dtn σ=_
      calc
        _=(B.dtn σ+B.dtn d+P.dtn σ)-B.dtn d := by abel
        _=_ := by rw [he]
    have hh := congrArg (nativeHighCoupledDtNInverse B P) he'
    rwa [nativeHighCoupledDtNInverse_left,hσh] at hh
  have hσ : NativeAngularSpectralRegular (3/2) (angularEmbedding σ) := by
    rw [hinv]
    convert (nativeHighCoupled_cauchy_spectral_regular B P d n (1/2)
      (by convert hdR using 1 <;> norm_num) hnR).1 using 1 <;> norm_num
  have hsd : NativeAngularSpectralRegular (3/2) (angularEmbedding (σ+d)) := by
    have h := (nativeAngularSpectralRegular_sub hσ (nativeAngularSpectralRegular_smul hdR (-1)).1).1
    simpa only [neg_one_smul,sub_neg_eq_add,map_add] using h
  let Ji := J+nativePoissonCollarJet P σ hσ
  let Ko := nativeLowCauchyCollarCLM ht (D,-N-(1/2:ℝ) • D)+nativePoissonExteriorCollarJet B (σ+d) hsd
  have hlow := nativeLowCauchyCollarCLM_traces ht D (-N-(1/2:ℝ) • D)
  have hln : nativeCollarNormalTraceCLM (nativeLowCauchyCollarCLM ht (D,-N-(1/2:ℝ) • D))=
      nativeAngularTraceCLM (nativeLowProjection N) := by
    have hh : -nativeLowProjection (-N-(1/2:ℝ) • D)-(1/2:ℝ) • nativeLowProjection D=nativeLowProjection N := by
      rw [map_sub,map_neg,map_smul]
      module
    rw [hlow.2,hh]
  have hvalue : nativeCollarValueTraceCLM Ji=nativeCollarValueTraceCLM Ko := by
    apply trace_injective
    simp only [Ji,Ko,map_add,nativePoissonCollarJet_value_trace,hlow.1,
      nativePoissonExteriorCollarJet_value_trace,nativeTraceAngular_left_inverse,
      P.curve_zero _ hσh,B.curve_zero _ hsdh]
    change D+angularEmbedding σ=nativeLowProjection D+(angularEmbedding σ+angularEmbedding d)
    rw [hdD]
    have h := nativeHighProjection_add_low D
    calc
      _=(nativeHighProjection D+nativeLowProjection D)+angularEmbedding σ := by rw [h]
      _=_ := by abel
  have hnormal : nativeCollarNormalTraceCLM Ji=nativeCollarNormalTraceCLM Ko := by
    apply trace_injective
    simp only [Ji,Ko,map_add,nativePoissonCollarJet_normal_trace,hln,
      nativePoissonExteriorCollarJet_normal_trace,nativeTraceAngular_left_inverse]
    unfold nativePoissonPhysicalEntranceNormal nativePoissonExteriorPhysicalEntranceNormal
    rw [P.curve_zero _ hσh,B.curve_zero _ hsdh,angularEmbedding.map_add]
    change N+(P.dtn σ-(1/2:ℝ) • angularEmbedding σ)=
      nativeLowProjection N+(-B.dtn (σ+d)-(1/2:ℝ) • (angularEmbedding σ+angularEmbedding d))
    have hn := nativeHighProjection_add_low N
    calc
      _=(nativeHighProjection N+nativeLowProjection N)+(P.dtn σ-(1/2:ℝ) • angularEmbedding σ) := by rw [hn]
      _=nativeLowProjection N-(B.dtn (σ+d)+P.dtn σ)+P.dtn σ-
        (1/2:ℝ) • (angularEmbedding σ+angularEmbedding d) := by
          rw [he]
          dsimp only [n]
          module
      _=_ := by abel
  exact ⟨d,σ,hdD,hdh,hσh,hsdh,hdR,hσ,hsd,he,hvalue,hnormal,
    nativeCollarWeakGluing_of_trace_equal Ji Ko hvalue hnormal,
    nativeCollarGluedFunction_local_H2 Ji Ko hvalue hnormal⟩

#print axioms exists_nativeSpectralJet_actual_matching
end Yamabe3.Analysis.SpherePolar
