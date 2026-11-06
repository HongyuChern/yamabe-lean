import Yamabe3.Analysis.NativeFeedbackCertificates
import Yamabe3.Analysis.OrderedNegativeReturnFeedback
import Yamabe3.Analysis.NativeShellCutoff

/-! Actual NEGATIVE-return feedback retaining the true smooth cutoff certificates.
This strengthened independent producer derives from the S018 source-level proof;
compact support and derivative support used in native energy assembly are retained.
The far cutoff is additionally chosen below b-1 so the ORIGINAL supported
outer source lies entirely in its plateau. This is proved by choosing the
far scale earlier, before fixing its geometric cost and the small physical scale.
The incoming and far maps are constructed from their proved producers,
not supplied as hypothetical small operators. Every source certificate
is retained. Physical PDE assembly/conormal cancellation is separate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic Delaunay
open Poincare.Analysis.Elliptic.Iteration
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def actualFeedbackH1Normed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] actualFeedbackH1Normed

theorem exists_nativeActual_negative_source_feedback_source_cutoff
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0 < R₀) (hsource:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) {τ:ℝ} (ht:0 < τ) :
    ∃(cTail:ℝ) (m n:ℕ) (b S δ CR:ℝ) (χin χout:E→ℝ)
      (hχin:ContDiff ℝ ∞ χin) (hχout:ContDiff ℝ ∞ χout),
      0 ≤ CR ∧ HasCompactSupport χin ∧ tsupport χin⊆ball (0:E) 3 ∧
      (∀x:E,0 ≤ χin x ∧ χin x ≤ 1) ∧ HasCompactSupport χout ∧
      (∀x:E,x∉nativeSourceShell → ∀i:Fin 3,
        partialDeriv i χout x=0 ∧ partialDeriv i (partialDeriv i χout) x=0) ∧
      0 < δ ∧ cTail < (m:ℝ)/2 ∧ b ≤ -(m:ℝ)/2-1 ∧
      S ≤ -(m:ℝ)/2-1 ∧ S ≤ b-1 ∧ -S+1/2 < ((m+n:ℕ):ℝ)/2 ∧
      (∀x∈closedBall (0:E) 2,χin=ᶠ[𝓝 x](fun _=>1)) ∧
      (∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χout=ᶠ[𝓝 x](fun _=>1)) ∧
      tsupport χout⊆ball (0:E) (Real.exp (1/8:ℝ)) ∧
      ∀a:ℝ,0 < a → a ≤ δ →
      ∀(B:M→ℝ) (hBs:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
        (hsmall:60*(∫x,|B x|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g),
      let Ω:=e '' ball (0:E) (a*64)
      ∀hΩ:IsOpen Ω,(∀x∈Ω,B x=0) →
      ∃(A:nativeSupportedSourcePairSpace b →L[ℝ] nativeSupportedSourcePairSpace b)
        (J:nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] RegularLowH4Space)
        (U:H1Zero g.leviCivitaData univ →L[ℝ] Lp AngularSpectralSpace 2 (volume:Measure ℝ))
        (I:nativeHomogeneousEnergySpace g B hBs Ω →L[ℝ] nativeSupportedSourcePairSpace b)
        (R:nativeSupportedSourcePairSpace b →L[ℝ] nativeHomogeneousEnergySpace g B hBs Ω)
        (T:nativeSupportedSourcePairSpace b →L[ℝ] nativeSupportedSourcePairSpace b),
        ‖A‖ ≤ 2 ∧ ‖T‖ ≤ 4 ∧ ‖R‖ ≤ CR*Real.sqrt a ∧
        (∀X,(A X).val=X.val+nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a (A X).val) ∧
        NativeIncomingSourceRealization g B hBs Ω hΩ gE e a τ cTail χin hχin
          (ball (0:E) (Real.exp cTail+1)) b J U I ∧
        NativeFarTailRealization g B hBs Ω gE e (closedBall (0:E) R₀) P hp v hv hb b ht
          a S cTail n (fun i:Fin n=>nativeOuterLogShellCenter (m+i.val)) χout hχout R ∧
        ∀X,(T X).val=X.val+
          nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a (T X).val+
          -(I (R (T X))).val := by
  let K:=closedBall (0:E) R₀
  have hK:IsCompact K := isCompact_closedBall _ _
  obtain ⟨χin,hχin,hχinc,hχins,hχrange,hχin1⟩:=exists_nativeIncoming_core_cutoff
  obtain ⟨χout,hχout,hχoutc,hχouts,hχout1,hχoutd⟩:=exists_nativeShellCutoff
  obtain ⟨cTail,N,hcTail,hN,hfar⟩:=exists_nativeCombined_far_tail_solver
    g hY gE hB hρ e he hei hK hsource P hp v hv hb ht 64 (by norm_num)
  obtain ⟨m,hm⟩:=exists_nat_gt (2*max cTail (Real.log 64+1)+2)
  have hmTail:cTail < (m:ℝ)/2 := by linarith [le_max_left cTail (Real.log 64+1)]
  have hmL:Real.log 64+1 < (m:ℝ)/2 := by linarith [le_max_right cTail (Real.log 64+1)]
  let b:=min (-(m:ℝ)/2-1) (nativeIncomingCutoffSlice.1-1/2)
  have hbm:b ≤ -(m:ℝ)/2-1 := min_le_left _ _
  have hbc:b ≤ nativeIncomingCutoffSlice.1-1/2 := min_le_right _ _
  let O:=ball (0:E) (Real.exp cTail+1)
  have hO:MeasurableSet O := measurableSet_ball
  have hvol:volume O < ⊤ := (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0:E) (Real.exp cTail+1)).measure_lt_top
  obtain ⟨dI,Ci,hdI,hCi,hinc⟩:=exists_nativeIncoming_same_field_supported_source g hY gE e he hei
    hR₀ hsource hcoeff hB hρ hK hsource τ (Real.log 128) cTail χin hχin hχrange hχin1 O hO hvol subset_rfl m hmTail b hbm hbc
  obtain ⟨dA,hdA,hdA1,hnear⟩:=exists_nativeSupportedFiniteWindow_source_inverse P hp v hv hb b ht m hbm
    ({()}:Finset Unit) (fun _=>gE) (fun _ _=>hB) (fun _ _=>hρ)
  obtain ⟨S₀,Ccut,hS₀,hCcut,hfarb⟩:=hfar b χout hχout hχoutd
  obtain ⟨S,hS,hSL,hgapFar⟩:=exists_ordered_feedback_far_scale Ci N Ccut (min S₀ (min (-(m:ℝ)/2-1) (b-1))) 64
    hCi hN.le hCcut (by norm_num)
  have hSS:S ≤ S₀ := hS.trans (min_le_left _ _)
  have hSm:S ≤ -(m:ℝ)/2-1 := hS.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSb:S ≤ b-1 := hS.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Mfar,hMf⟩:=exists_nat_gt (max ((m:ℝ)+2) (-2*S+2))
  have hmMf:m ≤ Mfar := by
    have hh:(m:ℝ) < Mfar := by linarith [le_max_left ((m:ℝ)+2) (-2*S+2)]
    exact Nat.le_of_lt (by exact_mod_cast hh)
  let n:=Mfar-m
  have hmn:m+n=Mfar := Nat.add_sub_of_le hmMf
  have hMcover:-S+1/2 < ((m+n:ℕ):ℝ)/2 := by
    rw [hmn]
    linarith [le_max_right ((m:ℝ)+2) (-2*S+2)]
  let t:Fin n→ℝ := fun i=>nativeOuterLogShellCenter (m+i.val)
  have hts (i:Fin n):t i ≤ 0 := by
    dsimp only [t,nativeOuterLogShellCenter]
    have hh:0 ≤ ((m+i.val:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  have hLt (i:Fin n):(64:ℝ) ≤ Real.exp (-t i-1/2) := by
    apply (Real.exp_log (by norm_num:(0:ℝ) < 64)).symm.trans_le
    apply Real.exp_le_exp.mpr
    dsimp only [t,nativeOuterLogShellCenter]
    have hh:(m:ℝ) ≤ ((m+i.val:ℕ):ℝ) := by exact_mod_cast Nat.le_add_right m i.val
    linarith
  obtain ⟨Cgeo,hCgeo,hfarA⟩:=hfarb S hSS hSL n t hts hLt
  obtain ⟨dF,hdF,hdF1,hgapSmall⟩:=exists_ordered_feedback_small_scale Ci N Cgeo hCi hN.le hCgeo
  let CR:=N*(Ccut*Real.exp (S/2)+Cgeo)
  have hCR:0 ≤ CR := by dsimp only [CR];positivity
  let H:=Real.exp cTail+1+64
  have hH:0 < H := by dsimp only [H];positivity
  let δ:=min dA (min dF (min (1/2:ℝ) (min (R₀/(2*H)) (min (dI/(1+Real.exp (Real.log 128))) (Real.exp (-(Mfar:ℝ)/2))))))
  have hδ:0 < δ := by dsimp only [δ];positivity
  refine ⟨cTail,m,n,b,S,δ,CR,χin,χout,hχin,hχout,hCR,hχinc,hχins,hχrange,hχoutc,hχoutd,
    hδ,hmTail,hbm,hSm,hSb,hMcover,hχin1,hχout1,hχouts,?_⟩
  intro a ha haδ B hBs hsmall
  dsimp only
  intro hΩ hzero
  have haA:a ≤ dA := haδ.trans (min_le_left _ _)
  have haF:a ≤ dF := haδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haHalf:a ≤ 1/2 := haδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have haR:a ≤ R₀/(2*H) := haδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have haI:a ≤ dI/(1+Real.exp (Real.log 128)) := haδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have haM:a ≤ Real.exp (-(Mfar:ℝ)/2) := haδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hfitBudget:a*(2*H) ≤ R₀ := (le_div_iff₀ (by positivity:0 < 2*H)).mp haR
  have ha64:a*64 ≤ R₀ := by dsimp only [H] at hfitBudget; nlinarith [Real.exp_pos cTail]
  have hfit:ball (0:E) (a*64)⊆e.source :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall ha64).trans hsource)
  have hKO:∀x∈O,a • x∈K := by
    intro x hx
    have hnx:‖x‖ < Real.exp cTail+1 := mem_ball_zero_iff.mp hx
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg ha.le]
    have hh:=mul_lt_mul_of_pos_left hnx ha
    dsimp only [H] at hfitBudget
    nlinarith [Real.exp_pos cTail]
  have hcore:a*Real.exp (Real.log 128)/2=a*64 := by rw [Real.exp_log (by norm_num:(0:ℝ) < 128)];ring
  have hscale:a*Real.exp (Real.log 128)/8 < dI := by
    have hh: a*(1+Real.exp (Real.log 128)) ≤ dI :=
      (le_div_iff₀ (by positivity:0 < 1+Real.exp (Real.log 128))).mp haI
    rw [Real.exp_log (by norm_num:(0:ℝ) < 128)] at hh ⊢
    linarith
  have hincA:=hinc a le_rfl ha haHalf (by rw [hcore];exact ha64) hscale hKO B hBs
  rw [hcore] at hincA
  obtain ⟨J,U,I,hI,hJv,hIv,hUv⟩:=hincA hΩ hzero
  have hr (i:Fin n):a*Real.exp (-t i) ≤ 1 := by
    have hni:m+i.val < Mfar := by
      have hh:m+i.val < m+n := Nat.add_lt_add_left i.isLt m
      simpa only [hmn] using hh
    have hh:((m+i.val:ℕ):ℝ)+1 ≤ Mfar := by exact_mod_cast hni
    have ht: -t i ≤ (Mfar:ℝ)/2 := by dsimp only [t,nativeOuterLogShellCenter];linarith
    apply (mul_le_mul haM (Real.exp_le_exp.mpr ht) (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
    rw [←Real.exp_add,neg_div,neg_add_cancel,Real.exp_zero]
  obtain ⟨R,hR,hRv⟩:=hfarA B hBs hsmall a ha hfit hr
  have hRbound:‖R‖ ≤ CR*Real.sqrt a := by
    apply hR.trans
    calc
      _ ≤ N*Real.sqrt a*(Ccut*Real.exp (S/2)+Cgeo) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_of_le_one_right hCgeo (haHalf.trans (by norm_num:(1/2:ℝ) ≤ 1)))) (by positivity)
      _ = _ := by dsimp only [CR];ring
  obtain ⟨A,hA,hAv⟩:=hnear a ha.le haA () (by simp)
  obtain ⟨T,hT,hTv⟩:=exists_two_scale_negative_return_feedback A I R Ci N Ccut Cgeo a S
    hCi hN.le ha hA hI hR hgapFar (hgapSmall a ha.le haF)
  refine ⟨A,J,U,I,R,T,hA,hT,hRbound,hAv,⟨hJv,hIv,hUv⟩,hRv,?_⟩
  intro X
  have hh:=hAv (X-I (R (T X)))
  rw [hTv X] at hh
  have he:(X-I (R (T X))).val=X.val-(I (R (T X))).val := rfl
  rw [he] at hh
  calc
    (T X).val=(X.val-(I (R (T X))).val)+
        nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a (T X).val := hh
    _=_ := by abel

#print axioms exists_nativeActual_negative_source_feedback_source_cutoff
end Yamabe3.Analysis.SpherePolar
