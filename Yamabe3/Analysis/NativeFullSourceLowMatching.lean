import Yamabe3.Analysis.NativeFullSourceBoundaryCorrection
import Yamabe3.Analysis.BubbleLowAngularCauchy

/-! Same-source boundary matching with the actual finite low compensations.
The exterior angular field is tied to both genuine traces of one interior
H2 collar jet. Native geometric feedback and exterior collar realization
remain separate obligations, not consequences of this model statement. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeFullSourceExteriorModel (t₀ : ℝ) (q : AngularIndex → ℝ → ℝ) (σ : AngularH1) (s : ℝ) : AngularL2 :=
  Real.exp (s/2) • (bubbleLowAngularCurve q (t₀+s)+(fullBubbleHighPotential (-t₀)).curve σ (-s))

variable (P : NativeHighPotential)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀ t,0 ≤ v t ∧ v t ≤ 1)

theorem exists_nativeFullSource_low_compensated_matching
    {t₀ : ℝ} (ht : 0 < t₀) (F : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    let B := fullBubbleHighPotential (-t₀)
    let σ := nativeFullSourceBoundarySigma B P hp v hv hb F
    let J := nativeFullSourceMatchedInteriorJet B P hp v hv hb F
    let d := nativeLowL2AngularCLM v hv hb F 0
    let N := nativeFullL2NormalAngularCLM P hp v hv hb F
    ∃ (c : AngularIndex → ℝ) (q : AngularIndex → ℝ → ℝ),
      (∀i∈nativeLowIndexFinset,
        c i=bubbleLowCauchyCompensation i t₀ (inner ℝ (angularBasis i) d)
          (inner ℝ (angularBasis i) (-N-(1/2:ℝ) • d)) 0 ∧
        ContDiff ℝ 2 (q i) ∧
        (∀t,deriv (deriv (q i)) t-bubbleLowCoefficient i t*q i t= -c i*bubbleCompensation i t) ∧
        Tendsto (q i) atBot (𝓝 0) ∧ Tendsto (deriv (q i)) atBot (𝓝 0)) ∧
      nativeFullSourceExteriorModel t₀ q σ 0=nativeTraceAngularCLM (nativeCollarValueTraceCLM J) ∧
      HasDerivWithinAt (nativeFullSourceExteriorModel t₀ q σ)
        (-nativeTraceAngularCLM (nativeCollarNormalTraceCLM J)) (Iic 0) 0 := by
  dsimp only
  let B := fullBubbleHighPotential (-t₀)
  let σ := nativeFullSourceBoundarySigma B P hp v hv hb F
  let J := nativeFullSourceMatchedInteriorJet B P hp v hv hb F
  let d := nativeLowL2AngularCLM v hv hb F 0
  let N := nativeFullL2NormalAngularCLM P hp v hv hb F
  let n := -N-(1/2:ℝ) • d
  have hd : nativeLowProjection d=d := nativeLowL2_entrance_is_low v hv hb F
  have hs : nativeHighEnergyProjectionCLM σ=σ := nativeFullSourceBoundarySigma_high B P hp v hv hb F
  obtain ⟨c,q,hq,hqv,hqn⟩ := exists_actual_angular_low_cauchy_solver (0 : ℝ →ᵇ AngularL2) ht d n
  have hqvalue : bubbleLowAngularCurve q t₀=d := hqv.trans hd
  have hn : nativeLowProjection n= -nativeLowProjection N-(1/2:ℝ) • d := by
    dsimp only [n]
    rw [map_sub,map_neg,map_smul,hd]
  have hderiv : HasDerivWithinAt
      (fun s : ℝ=>bubbleLowAngularCurve q (t₀+s)+B.curve σ (-s))
      (nativeLowProjection n+B.dtn σ) (Iic 0) 0 := by
    have h : HasDerivAt (bubbleLowAngularCurve q) (nativeLowProjection n) (t₀+0) := by simpa using hqn
    exact (h.comp_const_add t₀ 0).hasDerivWithinAt.add (B.reflected_curve_left_derivative σ)
  have hamp : HasDerivAt (fun s : ℝ=>Real.exp (s/2)) (1/2:ℝ) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).div_const 2).exp using 1 <;> norm_num
  have hout := hamp.hasDerivWithinAt.smul hderiv
  have hvJ := (nativeFullSourceMatchedInterior_traces B P hp v hv hb F).1
  have hnJ := (nativeFullSourceMatchedInterior_traces B P hp v hv hb F).2
  have hcouple := nativeFullSourceBoundarySigma_equation B P hp v hv hb F
  have hdecomp := nativeHighProjection_add_low N
  have hzero (t : ℝ) : (0 : ℝ →ᵇ AngularL2) t=0 := rfl
  refine ⟨c,q,?_,?_,?_⟩
  · intro i hi
    refine ⟨?_,(hq i hi).2.1,?_,(hq i hi).2.2.2.2.2⟩
    · have h := (hq i hi).1
      simpa only [bubbleLowSourceMoment,bubbleSourceCoordinate_apply,hzero,
        inner_zero_right,mul_zero,integral_zero] using h
    · intro t
      have h := (hq i hi).2.2.1 t
      simpa only [hzero,inner_zero_right,mul_zero,zero_add,neg_mul] using h
  · change Real.exp (0/2) • (bubbleLowAngularCurve q (t₀+0)+B.curve σ (-0))=_
    rw [zero_div,Real.exp_zero,one_smul,add_zero,neg_zero,hqvalue,B.curve_zero _ hs]
    exact hvJ.symm
  · change HasDerivWithinAt (nativeFullSourceExteriorModel t₀ q σ) _ (Iic 0) 0 at hout
    apply hout.congr_deriv
    simp only [zero_div,Real.exp_zero,one_smul,add_zero,neg_zero,hqvalue,B.curve_zero _ hs]
    rw [hn,add_comm (-nativeLowProjection N-(1/2:ℝ) • d+B.dtn σ)]
    change (1/2:ℝ) • (d+angularEmbedding σ)+(-nativeLowProjection N-(1/2:ℝ) • d+B.dtn σ)=
      -nativeTraceAngularCLM (nativeCollarNormalTraceCLM J)
    rw [hnJ]
    change B.dtn σ+P.dtn σ= -nativeHighProjection N at hcouple
    have hsum : B.dtn σ+P.dtn σ+N-nativeLowProjection N=0 := by
      rw [hcouple]
      calc
        -nativeHighProjection N+N-nativeLowProjection N= -(nativeHighProjection N+nativeLowProjection N)+N := by abel
        _ = 0 := by rw [hdecomp];abel
    rw [smul_add]
    have he : (1/2:ℝ) • d+(1/2:ℝ) • angularEmbedding σ+
        (-nativeLowProjection N-(1/2:ℝ) • d+B.dtn σ)=
        (B.dtn σ+P.dtn σ+N-nativeLowProjection N)-
          (N+P.dtn σ-(1/2:ℝ) • angularEmbedding σ) := by abel
    rw [he,hsum,zero_sub]

#print axioms exists_nativeFullSource_low_compensated_matching
end Yamabe3.Analysis.SpherePolar
