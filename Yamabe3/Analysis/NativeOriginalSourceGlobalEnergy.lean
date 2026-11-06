import Yamabe3.Analysis.NativeFullTrueEntranceSolver
import Yamabe3.Analysis.NativeH4MatchedExteriorAllScale
import Yamabe3.Analysis.NativeMatchedGlobalEnergy

/-! A genuine original weighted H2 source produces ONE matched global
Euclidean energy element. The baseline source stays in its original
space. Every annulus and the completion represent the SAME inner field
and actual outer field, including all four low compensations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD

theorem exists_originalSource_matched_global_energy
    {κ:ℝ} (hκ0:0 ≤ κ) (hκ1:κ < 1) (p:DelaunayPhaseData κ)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|) ≤ κ)
    {τ:ℝ} (ht:0 < τ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1)) (N:ℕ) :
    let P:=p.nativeHighPotential hκ0 hκ1
    ∃(T:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
      (L:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero Deuc univ),
      ∀f:HalfEndPhysicalH2SourceGraph,∃F:E→ℝ,∃hF2:ContDiffOn ℝ 2 F ({0}ᶜ:Set E),
        EqOn (nativeH4GraphFunction (T f)) F (closedBall (0:E) 4) ∧
        (F=ᵐ[volume.restrict (ball (0:E) 1\{0})]fullModelPhysicalField hκ0 hκ1 p f) ∧
        ∃qi wo:ℝ×SpherePolar.S→ℝ,Measurable qi ∧ Measurable wo ∧
          (∀i:HalfEndPhysicalSliceIndex,
            ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T f)).val.1:E→ℝ)
              =ᵐ[volume.restrict nativePoissonEntranceCollar]
                fun x=>Real.exp (3*i.val/2)*(F (Real.exp (-i.val) • x)+cylinderLift qi (Real.exp (-i.val) • x))) ∧
          (∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T f) s) s wo) ∧
          (toL2 Deuc univ (L f):E→ℝ)=ᵐ[volume]
            fun y=>nativeOuterCollarCutoff χ (N+1) y*
              (ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y := by
  dsimp only
  let P:=p.nativeHighPotential hκ0 hκ1
  let B:=fullBubbleHighPotential (-τ)
  obtain ⟨M,hM,hS⟩:=exists_uniform_full_true_entrance_H4_solver hκ0 hκ1
  obtain ⟨T,hT,hTf⟩:=hS p
  let F:HalfEndPhysicalH2SourceGraph→E→ℝ:=fun f=>(hTf f).choose
  have hF (f:HalfEndPhysicalH2SourceGraph):Continuous (F f) ∧ ContDiffOn ℝ 2 (F f) ({0}ᶜ:Set E) ∧
      F f 0=0 ∧ EqOn (nativeH4GraphFunction (T f)) (F f) (closedBall (0:E) 4) ∧
      (F f=ᵐ[volume.restrict (ball (0:E) 1\{0})]fullModelPhysicalField hκ0 hκ1 p f):=by
    exact ⟨(hTf f).choose_spec.1,(hTf f).choose_spec.2.1,(hTf f).choose_spec.2.2.1,
      (hTf f).choose_spec.2.2.2.1,(hTf f).choose_spec.2.2.2.2.1⟩
  let qi:HalfEndPhysicalH2SourceGraph→ℝ×SpherePolar.S→ℝ:=fun f=>
    (nativeH4MatchedScale_same_field B P hp (T f) (F f) (hF f).2.2.2.1).choose
  have hqi (f:HalfEndPhysicalH2SourceGraph):Measurable (qi f) ∧
      ∀i:HalfEndPhysicalSliceIndex,((nativeH4MatchedScaleJetCLM B P hp i (T f)).val.1:E→ℝ)
        =ᵐ[volume.restrict nativePoissonEntranceCollar]
          fun x=>Real.exp (3*i.val/2)*(F f (Real.exp (-i.val) • x)+cylinderLift (qi f) (Real.exp (-i.val) • x)):=by
    have hh:=(nativeH4MatchedScale_same_field B P hp (T f) (F f) (hF f).2.2.2.1).choose_spec
    exact ⟨hh.1,hh.2.2⟩
  let wo:HalfEndPhysicalH2SourceGraph→ℝ×SpherePolar.S→ℝ:=fun f=>
    (exists_nativeH4MatchedExteriorAllScale_same_field P ht (T f)).choose
  have hwo (f:HalfEndPhysicalH2SourceGraph):Measurable (wo f) ∧
      ∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T f) s) s (wo f):=
    (exists_nativeH4MatchedExteriorAllScale_same_field P ht (T f)).choose_spec
  let ui:=fun f x=>F f x+cylinderLift (qi f) x
  let uo:=fun f=>cylinderLift (wo f)
  obtain ⟨C,hC,hbound⟩:=exists_nativeH4MatchedScale_bound B P hp
  let idx:ℕ→HalfEndPhysicalSliceIndex:=fun n=>⟨(((n+1:ℕ):ℝ)/4),
    (neg_nonpos.mpr (Real.log_nonneg (by norm_num))).trans (by positivity)⟩
  let J:=fun n=>(nativeH4MatchedScaleJetCLM B P hp (idx n)).comp T
  have hJ (n:ℕ):‖J n‖ ≤ C*‖T‖:=by
    apply (J n).opNorm_le_bound (by positivity)
    intro f
    change ‖(nativeH4MatchedScaleRawJetCLM B P hp (idx n)) (T f)‖ ≤ _
    exact (((nativeH4MatchedScaleRawJetCLM B P hp (idx n)).le_of_opNorm_le (hbound _) _).trans
      (mul_le_mul_of_nonneg_left (T.le_opNorm f) hC.le)).trans_eq (by ring)
  obtain ⟨D,hD,houter⟩:=exists_nativeH4MatchedExteriorAllScale_bound P ht
  have hneg (i:Fin N):-((i.val+2:ℕ):ℝ)/4 ≤ 0:=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num)
  let K:=fun i:Fin N=>((houter (-((i.val+2:ℕ):ℝ)/4) (hneg i)).choose).comp T
  let Ji:=(nativeH4MatchedScaleJetCLM B P hp nativeH4GraphZeroScale).comp T
  let Ko:=(nativeH4MatchedExteriorJetCLM P ht).comp T
  have hvv (f:HalfEndPhysicalH2SourceGraph):nativeCollarValueTraceCLM (Ji f)=nativeCollarValueTraceCLM (Ko f):=
    (nativeH4Matched_actual_matching P hp ht (T f) ⟨F f,(hF f).2.1⟩ (hF f).2.2.2.1).1
  have hi0 (f:HalfEndPhysicalH2SourceGraph):((Ji f).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]ui f:=by
    simpa only [Ji,ContinuousLinearMap.comp_apply,nativeH4GraphZeroScale,mul_zero,zero_div,neg_zero,
      Real.exp_zero,one_mul,one_smul,ui] using (hqi f).2 nativeH4GraphZeroScale
  have ho0 (f:HalfEndPhysicalH2SourceGraph):((Ko f).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]uo f:=by
    have hh:=(hwo f).2 0
    rw [nativeH4MatchedExteriorAllScale_zero] at hh
    simpa only [Ko,ContinuousLinearMap.comp_apply,NativeScaledJetRep,mul_zero,zero_div,neg_zero,
      Real.exp_zero,one_mul,one_smul,uo] using hh
  have hi (n:ℕ) (f:HalfEndPhysicalH2SourceGraph):((J n f).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*(((n+1:ℕ):ℝ)/4)/2)*ui f (Real.exp (-(((n+1:ℕ):ℝ)/4)) • y):=(hqi f).2 (idx n)
  have ho (i:Fin N) (f:HalfEndPhysicalH2SourceGraph):((K i f).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun y=>Real.exp (3*(-((i.val+2:ℕ):ℝ)/4)/2)*uo f (Real.exp (-(-((i.val+2:ℕ):ℝ)/4)) • y):=by
    change (((houter _ (hneg i)).choose (T f)).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] _
    rw [(houter _ (hneg i)).choose_spec.2]
    exact (hwo f).2 _
  obtain ⟨L,hL⟩:=exists_nativeMatched_global_energy_family χ hχ hc hs h1 N J K Ji Ko
    (mul_nonneg hC.le (norm_nonneg T)) hJ hvv ui uo hi0 ho0 hi ho
  exact ⟨T,L,fun f=>⟨F f,(hF f).2.1,(hF f).2.2.2.1,(hF f).2.2.2.2,
    qi f,wo f,(hqi f).1,(hwo f).1,(hqi f).2,(hwo f).2,hL f⟩⟩

#print axioms exists_originalSource_matched_global_energy
end Yamabe3.Analysis.UniformElliptic
