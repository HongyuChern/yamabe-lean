import Yamabe3.Analysis.NativeOriginalSourceCoupledFeedback
import Yamabe3.Analysis.NativeOrderedEnergyFeedbackBundle
import Yamabe3.Analysis.NativeOriginalFeedbackEnergyBundle
import Yamabe3.Analysis.NativeH4SharedFarReturn
import Yamabe3.Analysis.NativeOriginalAffineFeedback

/-! An ACTUAL original-H4 baseline far return and its affine source
feedback on the SAME tail, native receiving space, cutoffs and scale.
The original weighted forcing remains outside whole-line L2. The
returned far equation and affine fixed equation are proved jointly;
the global native field/PDE and conormal identity remain separate gates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def originalFeedbackNormed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] originalFeedbackNormed

theorem exists_nativeOriginalSource_energy_coupled_feedback_ordered
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
    ∃(cTail:ℝ) (m n:ℕ) (b S δ CR CM Cbase CY N CI:ℝ) (χin χout:E→ℝ)
      (hχin:ContDiff ℝ ∞ χin) (hχout:ContDiff ℝ ∞ χout),
      0<N ∧ 0≤CI ∧ NativeEnergyReceivingTailSolver g e (closedBall (0:E) R₀) τ 64 cTail N ∧
      Real.log 128 ≤ cTail ∧ Real.log 64+1 < (m:ℝ)/2 ∧ S ≤ -τ-3 ∧
      0 < δ ∧ 0 ≤ Cbase ∧ 0 ≤ CY ∧ ∀a:ℝ,∀ha:0 < a,a ≤ δ → ∃ha1:a ≤ 1,
        ∃W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
          (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
          (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
          (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1,
        ‖W.I‖≤CI*Real.exp (-Real.log a/2) ∧
        ∃Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)),
          ‖Rbase‖ ≤ Cbase*Real.sqrt a ∧
          NativeH4BaselineFarRealization g gE e (closedBall (0:E) R₀) P ht a S cTail m n χout hχout Rbase ∧
          let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase
          ‖Y‖ ≤ CY ∧ ∀x:HalfEndPhysicalH4Graph,
            (Y x).val=nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a x+
              nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a (Y x).val-
              (W.I (Rbase x+W.R (Y x))).val := by
  let K:=closedBall (0:E) R₀
  let SH4:=(exists_nativeH4_uniform_cutoff_source_threshold g gE e he hei (isCompact_closedBall (0:E) R₀) hsource P ht).choose
  obtain ⟨cTail,m,n,b,S,d₀,CR,CM,N,CI,χin,χout,hχin,hχout,hTailBound,hN,hCI,hEnergyReceiver,hReceiver,hmL,hS,hδ₀,hCR,hCM,hW⟩:=
    exists_nativeActual_completed_feedback_with_energy_receiver_ordered (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
      (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb) (τ:=τ) (ht:=ht)
      hY hR₀ hcoeff hB hρ (min SH4 (-τ-3))
  have hSL:(64:ℝ) ≤ Real.exp (-S-1/2):=by
    obtain ⟨h₁,W,hI⟩:=hW (d₀/2) (by linarith) (by linarith)
    apply (Real.exp_log (by norm_num:(0:ℝ) < 64)).symm.trans_le
    apply Real.exp_le_exp.mpr
    linarith [W.source_cutoff,W.near_support]
  let t:Fin n→ℝ:=fun i=>nativeOuterLogShellCenter (m+i.val)
  have hts (i:Fin n):t i ≤ 0:=by
    dsimp only [t,nativeOuterLogShellCenter]
    have hh:0 ≤ ((m+i.val:ℕ):ℝ):=Nat.cast_nonneg _
    linarith
  have hLt (i:Fin n):(64:ℝ) ≤ Real.exp (-t i-1/2):=by
    apply (Real.exp_log (by norm_num:(0:ℝ) < 64)).symm.trans_le
    apply Real.exp_le_exp.mpr
    dsimp only [t,nativeOuterLogShellCenter]
    have hh:(m:ℝ) ≤ ((m+i.val:ℕ):ℝ):=by exact_mod_cast Nat.le_add_right m i.val
    linarith
  obtain ⟨Ccut,hCcut,hcut⟩:=exists_nativeH4_far_return_of_shared_receiver g gE hB hρ e he hei
    (isCompact_closedBall (0:E) R₀) hsource P ht 64 cTail N hN.le hReceiver χout hχout
  obtain ⟨Cgeo,hCgeo,hfar⟩:=hcut S (hS.trans (min_le_left _ _)) hSL n t hts hLt
  obtain ⟨dN,Cnear,hdN,hdN1,hCnear,hnear⟩:=exists_nativeH4FiniteWindowGlobalSource_bound P hp ht m
    ({()}:Finset Unit) (fun _=>gE) (fun _ _=>hB) (fun _ _=>hρ)
  let δ:=min d₀ (min dN (min 1 (Real.exp (-((m+n:ℕ):ℝ)/2))))
  let Cbase:=N*(Ccut*Real.exp (S/2)+Cgeo)
  let CY:=4*(Cnear+CI*Cbase)
  have hδ:0 < δ:=by dsimp only [δ];positivity
  have hCbase:0 ≤ Cbase:=by dsimp only [Cbase];positivity
  have hCY:0 ≤ CY:=by dsimp only [CY];positivity
  refine ⟨cTail,m,n,b,S,δ,CR,CM,Cbase,CY,N,CI,χin,χout,hχin,hχout,hN,hCI,hEnergyReceiver,hTailBound,hmL,hS.trans (min_le_right _ _),hδ,hCbase,hCY,fun a ha had=>?_⟩
  obtain ⟨ha1,W,hI⟩:=hW a ha (had.trans (min_le_left _ _))
  have haN:a ≤ dN:=had.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haM:a ≤ Real.exp (-((m+n:ℕ):ℝ)/2):=had.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hfit:ball (0:E) (a*64)⊆e.source:=ball_subset_closedBall.trans
    ((closedBall_subset_closedBall W.receiving_fit).trans hsource)
  have hr (i:Fin n):a*Real.exp (-t i) ≤ 1:=by
    have hni:m+i.val < m+n:=Nat.add_lt_add_left i.isLt m
    have hh:((m+i.val:ℕ):ℝ)+1 ≤ ((m+n:ℕ):ℝ):=by exact_mod_cast hni
    have ht:-t i ≤ ((m+n:ℕ):ℝ)/2:=by dsimp only [t,nativeOuterLogShellCenter];linarith
    apply (mul_le_mul haM (Real.exp_le_exp.mpr ht) (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
    rw [←Real.exp_add,neg_div,neg_add_cancel,Real.exp_zero]
  have hsmall:60*(∫x,|(0:ℝ)|^6 ∂g.volumeMeasure)^(2/3:ℝ) ≤ Target.yamabeConstant g:=by simpa using hY.le
  obtain ⟨Rbase,hRb,hRv⟩:=hfar (fun _:M=>0) contMDiff_const hsmall a ha hfit hr
  have hRbase:‖Rbase‖ ≤ Cbase*Real.sqrt a:=by
    apply hRb.trans
    calc
      _ ≤ N*Real.sqrt a*(Ccut*Real.exp (S/2)+Cgeo):=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_of_le_one_right hCgeo ha1)) (by positivity)
      _ = _:=by dsimp only [Cbase];ring
  let B₀:=nativeActualH4BaselineResidualCLM W
  have hB₀:‖B₀‖ ≤ Cnear*a:=
    (nativeH4SupportedWindowSource_norm P hp ht m gE a b W.near_support).trans (hnear a ha.le haN () (by simp))
  have hB₁:‖B₀‖ ≤ Cnear:=hB₀.trans (mul_le_of_le_one_right hCnear.le ha1)
  have hIR:‖W.I‖*‖Rbase‖ ≤ CI*Cbase:=by
    apply (mul_le_mul hI hRbase (norm_nonneg Rbase) (by positivity)).trans_eq
    calc
      _ = (CI*Cbase)*(Real.exp (-Real.log a/2)*Real.sqrt a):=by ring
      _ = _:=by rw [exp_negative_half_log_mul_sqrt ha,mul_one]
  refine ⟨ha1,W,hI,Rbase,hRbase,hRv,?_,?_⟩
  · exact (nativeOriginalAffineFeedback_norm W B₀ Rbase).trans
      (mul_le_mul_of_nonneg_left (add_le_add hB₁ hIR) (by norm_num))
  · intro x
    exact nativeOriginalAffineFeedback_fixed W B₀ Rbase x

#print axioms exists_nativeOriginalSource_energy_coupled_feedback_ordered
end Yamabe3.Analysis.SpherePolar
