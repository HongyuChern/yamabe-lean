import Yamabe3.Analysis.NativeH4MatchedAllScale
import Yamabe3.Analysis.NativeH4GraphTraceIdentity
import Yamabe3.Analysis.NativeExteriorBoundaryOperators

/-! Bounded linear inner and outer jets of one original H4 field.
The outer low Cauchy producer retains the actual computed compensation.
Identification with the proved matching witnesses uses the same literal
C2 function, not an a.e. restriction to the sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  {τ : ℝ} (ht : 0<τ)

def nativeH4GraphZeroScale : HalfEndPhysicalSliceIndex :=
  ⟨0,neg_nonpos.mpr (Real.log_nonneg (by norm_num))⟩

theorem nativeH4GraphExteriorDatum_spectral_bound (B : NativeHighPotential) :
    ∃D : ℝ,0≤D ∧ ∀v,(∑'i,nativeAngularWeightedSquare (3/2)
      (angularEmbedding (nativeH4GraphExteriorDatumCLM B P v)) i)≤D*‖v‖^2 := by
  obtain ⟨D,hD,h⟩ := exists_nativeH4Graph_coupling_energy_bound B
  refine ⟨D,hD,fun v => ?_⟩
  have he := (h P v).2
  unfold nativePoissonBoundaryEnergy at he
  linarith [sq_nonneg ‖nativeH4GraphExteriorDatumCLM B P v‖]

def nativeH4MatchedExteriorJetCLM : HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure :=
  (nativeLowCauchyCollarCLM ht).comp
    (nativeH4GraphAngularValueCLM.prod (-nativeH4GraphAngularNormalCLM-(1/2:ℝ) • nativeH4GraphAngularValueCLM))+
  nativeExteriorBoundaryJetCLM (fullBubbleHighPotential (-τ))
    (nativeH4GraphExteriorDatumCLM (fullBubbleHighPotential (-τ)) P)
    (nativeH4GraphExteriorDatum_regular (fullBubbleHighPotential (-τ)) P)
    (nativeH4GraphExteriorDatum_spectral_bound P (fullBubbleHighPotential (-τ)))

theorem nativeH4MatchedScale_zero (B : NativeHighPotential) (v : HalfEndPhysicalH4Graph)
    (u : nativeC2OffZero) (hu : EqOn (nativeH4GraphFunction v) u.val (closedBall (0:E) 4)) :
    nativeH4MatchedScaleJetCLM B P hp nativeH4GraphZeroScale v=
      nativeC2CollarJetInclusion u+nativePoissonCollarJet P (nativeH4GraphSigmaCLM B P v)
        (nativeH4GraphSigma_regular B P v) := by
  let b := nativeH4GraphSigmaCLM B P v
  have hspec := nativeH4GraphSigma_regular B P v
  have hbase := nativeH4GraphScaleJet_zero_C2 v u hu
  have he : nativeBoundaryPoissonJetCLM P hp (nativeH4GraphSigmaCLM B P)
      (nativeH4GraphSigma_regular B P) (nativeH4GraphSigma_energy_bound B P) 0 v=nativePoissonCollarJet P b hspec := by
    obtain ⟨w,hw,hae,_⟩ := nativePoissonReflectedCurve_joint_representative P b
    have hs := nativePoissonAllScaleValue_same_field P hp b hspec hw.measurable hae 0
    have he := nativePoissonCollarValue_eq_lift P b hspec hw.measurable hae
    apply nativeCollarJet_value_injective
    apply Lp.ext
    have hs0 : (nativePoissonAllScaleValue P hp 0 b : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] cylinderLift w := by
      simpa only [mul_zero,zero_div,neg_zero,Real.exp_zero,one_mul,one_smul] using hs
    exact hs0.trans he.symm
  change nativeH4GraphScaleJetCLM nativeH4GraphZeroScale v+
    nativeBoundaryPoissonJetCLM P hp (nativeH4GraphSigmaCLM B P)
      (nativeH4GraphSigma_regular B P) (nativeH4GraphSigma_energy_bound B P) 0 v=_
  rw [he]
  change nativeH4GraphScaleJetCLM nativeH4GraphZeroScale v=nativeC2CollarJetInclusion u at hbase
  rw [hbase]

theorem nativeH4Matched_actual_matching (v : HalfEndPhysicalH4Graph)
    (u : nativeC2OffZero) (hu : EqOn (nativeH4GraphFunction v) u.val (closedBall (0:E) 4)) :
    let J := nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp nativeH4GraphZeroScale v
    let K := nativeH4MatchedExteriorJetCLM P ht v
    nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K ∧
      nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K ∧
      NativeCollarWeakGluing J K ∧
      MemWkpLocally 2 (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar := by
  let B := fullBubbleHighPotential (-τ)
  have hspec := nativeC2_actual_trace_spectral u
  obtain ⟨d,σ,hd,hph,hsh,hsdh,hdR,hsR,hsdR,hc,hval,hnorm,hglue,hH2⟩ :=
    exists_nativeSpectralJet_actual_matching P ht (nativeC2CollarJetInclusion u) hspec.1 hspec.2
  have hw := nativeH4Graph_coupled_witness_identity B P v u hu d σ hd hsh hc
  rcases hw with ⟨rfl,rfl⟩
  have htrace := nativeH4Graph_trace_agrees_C2 v u hu
  have hJ := nativeH4MatchedScale_zero P hp B v u hu
  have hK : nativeH4MatchedExteriorJetCLM P ht v=
      nativeLowCauchyCollarCLM ht
        (nativeTraceAngularCLM (nativeCollarValueTraceCLM (nativeC2CollarJetInclusion u)),
        -nativeTraceAngularCLM (nativeCollarNormalTraceCLM (nativeC2CollarJetInclusion u))-
          (1/2:ℝ) • nativeTraceAngularCLM (nativeCollarValueTraceCLM (nativeC2CollarJetInclusion u)))+
      nativePoissonExteriorCollarJet B (nativeH4GraphSigmaCLM B P v+nativeH4GraphHighValueCLM v) hsdR := by
    change nativeLowCauchyCollarCLM ht (nativeH4GraphAngularValueCLM v,-nativeH4GraphAngularNormalCLM v-
      (1/2:ℝ) • nativeH4GraphAngularValueCLM v)+
      nativePoissonExteriorCollarJet B (nativeH4GraphSigmaCLM B P v+nativeH4GraphHighValueCLM v) hsdR=_
    rw [htrace.1,htrace.2]
  dsimp only
  rw [hJ,hK]
  exact ⟨hval,hnorm,hglue,hH2⟩

#print axioms nativeH4GraphExteriorDatum_spectral_bound
#print axioms nativeH4MatchedScale_zero
#print axioms nativeH4Matched_actual_matching
end Yamabe3.Analysis.UniformElliptic
