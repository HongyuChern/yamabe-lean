import Yamabe3.Analysis.NativeH4MatchedErrorFeedback
import Yamabe3.Analysis.NativeMatchedCollarRegularity

/-! Adding the one supported residual solution preserves the actual
matching traces and represents one common field on all inner scales.
These identities are proved for the constructed jets; they do not claim
higher regularity from arbitrary H1 boundary data. -/
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
  (v₀ : ℝ→ℝ) (hv : Continuous v₀) (hb : ∀t,0≤v₀ t ∧ v₀ t≤1)
  (b : ℝ) {τ : ℝ} (ht : 0<τ)
  (T : HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource)

def nativeH4CorrectedScaleJetCLM (i : HalfEndPhysicalSliceIndex) : HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure :=
  nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i+
    (nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ i.1).comp T

def nativeH4CorrectedExteriorJetCLM : HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure :=
  nativeH4MatchedExteriorJetCLM P ht+(nativeSupportedTwoSidedExteriorJetCLM P hp v₀ hv hb b ht).comp T

theorem nativeH4Corrected_actual_matching (x : HalfEndPhysicalH4Graph) (u : nativeC2OffZero)
    (hu : EqOn (nativeH4GraphFunction x) u.val (closedBall (0:E) 4)) :
    let J := nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T nativeH4GraphZeroScale x
    let K := nativeH4CorrectedExteriorJetCLM P hp v₀ hv hb b ht T x
    nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K ∧
      nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K ∧
      NativeCollarWeakGluing J K ∧
      MemWkpLocally 2 (nativeCollarGluedFunction J.val.1 K.val.1) nativePoissonEntranceCollar := by
  have hm := nativeH4Matched_actual_matching P hp ht x u hu
  have hc := nativeSupportedTwoSidedSource_actual_matching P hp v₀ hv hb b ht (T x)
  let J := nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T nativeH4GraphZeroScale x
  let K := nativeH4CorrectedExteriorJetCLM P hp v₀ hv hb b ht T x
  have hval : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K := by
    change nativeCollarValueTraceCLM (_+_)=nativeCollarValueTraceCLM (_+_)
    rw [map_add,map_add]
    exact congrArg₂ (·+·) hm.1 hc.1
  have hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K := by
    change nativeCollarNormalTraceCLM (_+_)=nativeCollarNormalTraceCLM (_+_)
    rw [map_add,map_add]
    exact congrArg₂ (·+·) hm.2.1 hc.2
  exact ⟨hval,hn,nativeCollarWeakGluing_of_trace_equal J K hval hn,
    nativeCollarGluedFunction_local_H2 J K hval hn⟩

theorem nativeH4Corrected_same_field (x : HalfEndPhysicalH4Graph) (F : E→ℝ)
    (hF : EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue x)) F (closedBall (0:E) 4)) :
    ∃w : ℝ×S→ℝ,Measurable w ∧ ∀i : HalfEndPhysicalSliceIndex,
      ((nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T i x).val.1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
        (fun y => Real.exp (3*i.1/2)*(F (Real.exp (-i.1) • y)+cylinderLift w (Real.exp (-i.1) • y))) := by
  obtain ⟨q,hq,hqa,hj⟩ := nativeH4MatchedScale_same_field (fullBubbleHighPotential (-τ)) P hp x F hF
  obtain ⟨w,hw,hwj⟩ := nativeTwoSidedAllScale_same_field P hp v₀ hv hb τ (T x)
  refine ⟨fun z => q z+w z,hq.add hw,fun i => ?_⟩
  have ha := Lp.coeFn_add (nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x).val.1
    (nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ i.1 (T x)).val.1
  filter_upwards [hj i,hwj i.1,ha] with y hj hwj ha
  change (((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x).val.1+
    (nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ i.1 (T x)).val.1 : NativeCollarL2) : E→ℝ) y=_
  rw [ha]
  change (nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x).val.1 y+
    (nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ i.1 (T x)).val.1 y=_
  change (nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x).val.1 y=
    Real.exp (3*i.1/2)*(F (Real.exp (-i.1) • y)+cylinderLift q (Real.exp (-i.1) • y)) at hj
  change (nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ i.1 (T x)).val.1 y=
    Real.exp (3*i.1/2)*cylinderLift w (Real.exp (-i.1) • y) at hwj
  rw [hj,hwj,native_cylinderLift_add]
  ring

theorem exists_nativeH4CorrectedScale_bound :
    ∃C : ℝ,0<C ∧ ∀i : HalfEndPhysicalSliceIndex,
      ‖nativeH4CorrectedScaleJetCLM P hp v₀ hv hb (τ:=τ) T i‖≤C := by
  obtain ⟨C,hC,hc⟩ := exists_nativeH4MatchedScale_bound (fullBubbleHighPotential (-τ)) P hp
  obtain ⟨D,hD,hd⟩ := exists_nativeTwoSidedAllScale_bound P hp v₀ hv hb τ
  refine ⟨C+D*‖T‖,by positivity,fun i => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)⟩
  have h1 := (nativeH4MatchedScaleRawJetCLM (fullBubbleHighPotential (-τ)) P hp i).le_of_opNorm_le (hc i) x
  have h2 := (nativeTwoSidedAllScaleRawJetCLM P hp v₀ hv hb τ i.1).le_of_opNorm_le (hd i.1) (T x)
  have h3 := mul_le_mul_of_nonneg_left (T.le_opNorm x) hD.le
  change ‖nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i x+
    nativeTwoSidedAllScaleJetCLM P hp v₀ hv hb τ i.1 (T x)‖≤_
  exact (norm_add_le _ _).trans ((add_le_add h1 (h2.trans h3)).trans_eq (by ring))

#print axioms nativeH4Corrected_actual_matching
#print axioms nativeH4Corrected_same_field
#print axioms exists_nativeH4CorrectedScale_bound
end Yamabe3.Analysis.UniformElliptic
