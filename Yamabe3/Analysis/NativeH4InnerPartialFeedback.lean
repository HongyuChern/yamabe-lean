import Yamabe3.Analysis.NativeH4LocalSourceEquation

/-! The actual INNER residual cancellation needs only the inner source
fixed point. The independent finite outer/far/incoming construction is
retained; no obsolete full-collar exterior fixed point is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic
attribute [local irreducible] nativeFullShellSourceReturnCLM nativeTwoSidedJacobianRowCLM
  nativeH4MatchedGeometricSourceTerm
section PartialInner
variable (P:NativeHighPotential)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v₀:ℝ→ℝ) (hv:Continuous v₀) (hb:∀t,0≤v₀ t ∧ v₀ t≤1)
  (b:ℝ) {τ:ℝ} (ht:0<τ)

include b ht in
theorem nativeH4MatchedResidual_partial_cancellation
    (hpot:P.potential=delaunayPhasePotentialBCF v₀ hv hb 0)
    {ι:Type*} (Λ:Finset ι) (g:ι→RiemannianMetric 3 E)
    (hB:∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ:∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε:ℝ) (hε:0≤ε) (hε1:ε≤1) (a:ι) (ha:a∈Λ)
    (x:HalfEndPhysicalH4Graph) (Y:NativeTwoSidedSource)
    (hY:Y.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε x+
      nativeTwoSidedInnerGlobalSourceCLM P hp v₀ hv hb τ (g a) ε Y)
    (G:Lp AngularSpectralSpace 2 (volume:Measure ℝ)) (hG0:∀ᵐt:ℝ∂volume,t≤0→G t=0) :
    HasSum (fun n=>inner ℝ (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeH4MatchedGeometricRowCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε
        (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n) x+
        nativeTwoSidedJacobianRowCLM P hp v₀ hv hb τ (g a) ε (nativeLogShellCenter n) Y)) G) 0:=by
  let A:=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε
  let B:=nativeFullCollarSourceReturnCLM.comp (nativeSupportedTwoSidedExteriorErrorCLM P hp v₀ hv hb b ht (g a) ε)
  let X':NativeTwoSidedSource:=(A x,Y.2-B Y)
  have hfix:Y=X'+nativeSupportedTwoSidedGlobalSourceCLM P hp v₀ hv hb b ht (g a) ε Y:=by
    apply Prod.ext
    · exact hY
    · change Y.2=(Y.2-B Y)+B Y
      abel
  have h1:=nativeH4MatchedResidual_pairing_hasSum P hp (τ:=τ) Λ g hB hρ ε hε hε1 a ha x G
  have h2:=nativeSupportedTwoSidedGlobal_fixed_pairing P hp v₀ hv hb b ht hpot Λ g hB hρ
    ε hε hε1 a ha X' Y hfix G hG0
  have he:inner ℝ (A x) G+ -inner ℝ X'.1 G=0:=add_neg_cancel _
  have hsum:=h1.add h2
  change HasSum _ (inner ℝ (A x) G+ -inner ℝ X'.1 G) at hsum
  rw [he] at hsum
  simpa only [map_add,inner_add_left,nativeH4MatchedGeometricSourceTerm,ContinuousLinearMap.comp_apply] using hsum

include b ht in
theorem nativeH4Residual_physical_zero_partial
    (hpot : P.potential=delaunayPhasePotentialBCF v₀ hv hb 0)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource)
    (hY : Y.1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε x+
      nativeTwoSidedInnerGlobalSourceCLM P hp v₀ hv hb τ (g a) ε Y) :
    let R := nativePhysicalShellAssembly (nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) (g a) ε x Y)
    MemLp R 2 (volume.restrict (Metric.ball 0 1 \ {(0:E)})) ∧
      R=ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})] (fun _ => 0) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeH4ResidualPhysicalRow_bound P hp v₀ hv hb (τ:=τ) Λ g hB hρ
  let U := nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) (g a) ε x Y
  have hU := hc ε hε hε1 a ha x Y
  have hCxy : 0≤C*(‖x‖+‖Y‖) := by positivity
  have hm := nativePhysicalShellAssembly_memLp U hCxy hU
  refine ⟨hm,?_⟩
  have hz : nativePhysicalShellAssembly U=ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})]
      (fun _ => -(0:ℝ)) := by
    apply nativePhysicalTest_ae_eq_negative hm MemLp.zero'
    intro φ hφ hcs hs
    have h0 : (0:E)∉tsupport φ := fun h => (hs h).2 (by simp)
    let G := nativePhysicalPairTestL2 φ hφ hcs h0
    have hsum := nativeH4MatchedResidual_partial_cancellation P hp v₀ hv hb b ht hpot Λ g hB hρ ε hε hε1 a ha x Y hY
      G (nativePhysicalPairTestL2_positive φ hφ hcs h0 hs)
    have ht' : HasSum (fun n => Real.exp (-5*nativeLogShellCenter n/2)*
        (∫y in nativeSourceShell,(U n : E→ℝ) y*φ (Real.exp (-nativeLogShellCenter n) • y))) 0 := by
      simpa only [U,nativeH4ResidualPhysicalRow,G,nativeFullShellSourceReturn_physical_test] using hsum
    have he := (nativePhysicalShellAssembly_test_hasSum U hCxy hU φ hφ.continuous hcs).unique ht'
    simpa only [zero_mul,integral_zero,neg_zero] using he
  simpa only [neg_zero] using hz

#print axioms nativeH4MatchedResidual_partial_cancellation
#print axioms nativeH4Residual_physical_zero_partial
end PartialInner

section OriginalPhase
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)
  (b : ℝ) {τ : ℝ} (ht : 0<τ)
local notation "P" => p.nativeHighPotential hκ0 hκ1
local notation "v₀" => (fun t => p.orbit (t+p.phase))
local notation "hv" => (p.smooth.continuous.comp (continuous_id.add continuous_const))
local notation "hb" => (fun t => p.bounded (t+p.phase))
local notation "O" => (Metric.ball (0:E) 1 \ {(0:E)})

include b ht in
theorem nativeH4Corrected_local_source_identity_partial
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (T : HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource) (x : HalfEndPhysicalH4Graph)
    (hfix : (T x).1=nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε x+
      nativeTwoSidedInnerGlobalSourceCLM P hp v₀ hv hb τ (g a) ε (T x))
    (F u : E→ℝ)
    (hF : EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue x)) F (Metric.closedBall (0:E) 4))
    (hu : ∀i : HalfEndPhysicalSliceIndex,
      ((nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T i x).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun y => Real.exp (3*i.1/2)*u (Real.exp (-i.1) • y))) :
    MemWkpLocally 2 u O ∧ ∀U : Set E,IsOpen U → IsCompact (closure U) → closure U⊆O →
      MemWkp 2 2 u U ∧ nativeWeakRescaledDelaunayJacobian U (g a) ε p.orbit p.phase u
        =ᵐ[volume.restrict U] nativeWeakFlatJacobian U p.orbit p.phase F := by
  have hpot : (P).potential=delaunayPhasePotentialBCF v₀ hv hb 0 := by
    apply BoundedContinuousFunction.ext
    intro t
    change (15/4)*p.orbit (t+p.phase)^4=(15/4)*p.orbit (t+0+p.phase)^4
    rw [add_zero]
  have hid := nativeH4Residual_same_physical_operators hκ0 hκ1 p hp τ (g a) ε T x F u hF hu
  have hz := (nativeH4Residual_physical_zero_partial P hp v₀ hv hb b ht hpot Λ g hB hρ ε hε hε1 a ha x (T x) hfix).2
  have hop : nativePhysicalWeakJacobian (g a) ε p.orbit p.phase u=ᵐ[volume.restrict O]
      nativePhysicalWeakFlatJacobian p.orbit p.phase F := by
    filter_upwards [hid,hz] with y hi hz
    exact sub_eq_zero.mp (hi.symm.trans hz)
  have hul := native_half_scale_jet_local_H2 (fun i => nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T i x) hu
  have hFl := native_half_scale_jet_local_H2 (fun i => nativeH4GraphScaleJetCLM i x)
    (fun i => nativeH4GraphScaleJet_same_function i x F hF)
  have huw (n : ℕ) := native_true_scale_jet_physical_H2 (nativeLogShellCenter n)
    (nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T
      (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n)) x)
    (hu (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n)))
  have hFw (n : ℕ) := native_true_scale_jet_physical_H2 (nativeLogShellCenter n)
    (nativeH4GraphScaleJetCLM (nativeH4NonnegativeScaleIndex _ (nativeLogShellCenter_nonneg n)) x)
    (nativeH4GraphScaleJet_same_function _ x F hF)
  refine ⟨hul,fun U hU hUc hUO => ?_⟩
  have huU := memWkp_on_precompact_of_locally hul hU hUc hUO
  have hFU := memWkp_on_precompact_of_locally hFl hU hUc hUO
  have hUN := nativePhysicalWeakJacobian_local hU huU huw (g a) ε p.orbit p.phase
  have hUF := nativePhysicalWeakFlatJacobian_local hU hFU hFw p.orbit p.phase
  have hs : U∩O=U := inter_eq_left.mpr (subset_closure.trans hUO)
  rw [hs] at hUN hUF
  have hopU : nativePhysicalWeakJacobian (g a) ε p.orbit p.phase u=ᵐ[volume.restrict U]
      nativePhysicalWeakFlatJacobian p.orbit p.phase F :=
    ae_mono (Measure.restrict_mono (subset_closure.trans hUO) le_rfl) hop
  exact ⟨huU,hUN.symm.trans (hopU.trans hUF)⟩

#print axioms nativeH4Corrected_local_source_identity_partial
end OriginalPhase
end Yamabe3.Analysis.UniformElliptic
