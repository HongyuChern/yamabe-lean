import Yamabe3.Analysis.NativeOrderedEnergySourceFeedback
import Yamabe3.Analysis.NativeOriginalModelEnergyRealization

/-! One ACTUALLY PRODUCED signed native completed field for the original
weighted H2 source. All baseline/correction/return maps share one source,
one tail and one receiving space. The uniform energy bound is proved;
the full native PDE and global quotient-conormal identity remain gates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def signedOriginalNormed (g:RiemannianMetric 3 M):NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] signedOriginalNormed

theorem exists_nativeOriginal_signed_energy_trace_producer
    (g:RiemannianMetric 3 M) (hY:0 < Target.yamabeConstant g) (gE:RiemannianMetric 3 E)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R₀:ℝ} (hR₀:0 < R₀) (hsource:closedBall (0:E) R₀⊆e.source)
    (hcoeff:∀x∈closedBall (0:E) R₀,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (hB:gE.euclideanCoefficients 0=innerSL ℝ) (hρ:gE.pullbackVolumeDensity id 0=1)
    {κ:ℝ} (hκ0:0 ≤ κ) (hκ1:κ < 1) (p:DelaunayPhaseData κ)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|) ≤ κ) {τ:ℝ} (ht:0 < τ) :
    let P:=p.nativeHighPotential hκ0 hκ1
    let v:=fun t=>p.orbit (t+p.phase)
    let hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
    let hb:∀t,0 ≤ v t ∧ v t ≤ 1:=fun t=>p.bounded (t+p.phase)
    ∃(cTail:ℝ) (m n:ℕ) (b S δ CR CM C N CI Ccore Cbase CY:ℝ) (χin χout:E→ℝ)
      (hχin:ContDiff ℝ ∞ χin) (hχout:ContDiff ℝ ∞ χout)
      (O:Set E) (T₀:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
      (L₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero Deuc O),
      0<N ∧ 0≤CI ∧ 0≤Ccore ∧ 0≤Cbase ∧ 0≤CY ∧ NativeEnergyReceivingTailSolver g e (closedBall (0:E) R₀) τ 64 cTail N ∧
      Real.log 128 ≤ cTail ∧ Real.log 64+1 < (m:ℝ)/2 ∧ S ≤ -τ-3 ∧
      0 < δ ∧ 0 ≤ C ∧ NativeOriginalModelEnergyRealization hκ0 hκ1 p hp ht χout S O T₀ L₀ ∧
      ∀a:ℝ,∀ha:0 < a,a ≤ δ → ∃ha1:a ≤ 1,
        ∃W:NativeActualFeedbackEnergyBundle (g:=g) (gE:=gE) (e:=e) (he:=he) (hei:=hei)
          (R₀:=R₀) (hsource:=hsource) (P:=P) (hp:=hp) (v:=v) (hv:=hv) (hb:=hb)
          (τ:=τ) (ht:=ht) (cTail:=cTail) (m:=m) (n:=n) (b:=b) (S:=S) (CR:=CR) (CM:=CM)
          (χin:=χin) (χout:=χout) (hχin:=hχin) (hχout:=hχout) a ha ha1,
        ‖W.I‖≤CI*Real.exp (-Real.log a/2) ∧
        (∀R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)),
          ‖energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val‖≤Ccore*‖R‖) ∧
        ∃(Rbase:HalfEndPhysicalH4Graph →L[ℝ] nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64)))
          (Q₀:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero g.leviCivitaData univ),
          ‖Rbase‖≤Cbase*Real.sqrt a ∧
          ‖nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase‖≤CY ∧
          NativeH4BaselineFarRealization g gE e (closedBall (0:E) R₀) P ht a S cTail m n χout hχout Rbase ∧
          (∀f,toL2 g.leviCivitaData univ (Q₀ f)=nativeCompactChartL2CLM g e he hei
            (isCompact_closedBall (0:E) R₀) hsource (euclideanL2DilationCLM ha ha1 (toL2 Deuc O (L₀ f)))) ∧
          ‖nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase‖ ≤ C*Real.sqrt a ∧
          let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase
          ∀x:HalfEndPhysicalH4Graph,(Y x).val=nativeH4FiniteWindowGlobalSourceCLM P hp ht m gE a x+
            nativeFiniteWindowGlobalSourceCLM P hp v hv hb b ht m gE a (Y x).val-
            (W.I (Rbase x+W.R (Y x))).val := by
  dsimp only
  let P:=p.nativeHighPotential hκ0 hκ1
  let v:=fun t=>p.orbit (t+p.phase)
  let hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
  let hb:∀t,0 ≤ v t ∧ v t ≤ 1:=fun t=>p.bounded (t+p.phase)
  obtain ⟨cTail,m,n,b,S,d₀,CR,CM,Cbase,CY,N,CI,χin,χout,hχin,hχout,hN,hCI,hEnergyReceiver,hTailBound,hmL,hSComp,hd₀,hCbase,hCY,hStage⟩:=
    exists_nativeOriginalSource_energy_coupled_feedback_ordered g hY gE e he hei hR₀ hsource hcoeff hB hρ P hp v hv hb ht
  obtain ⟨ha₀1,W₀,hI₀,Rb₀,hRb₀,hRF₀,hYC₀,hFix₀⟩:=hStage (d₀/2) (by linarith) (by linarith)
  let H:=Real.exp ((1/8:ℝ)-S)+1
  have hH:0 < H:=by dsimp only [H];positivity
  let O:=ball (0:E) H
  have hO:tsupport (fun y:E=>χout (Real.exp S • y))⊆O:=by
    apply (nativeScaledCutoff_support W₀.outer_support S).trans
    apply ball_subset_ball
    dsimp only [H]
    rw [←Real.exp_add]
    simpa only [sub_eq_add_neg] using (le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num):
      Real.exp ((1/8:ℝ)+(-S)) ≤ Real.exp ((1/8:ℝ)+(-S))+1)
  obtain ⟨T₀,L₀,C₀,hC₀,hModel,hLift⟩:=exists_originalSource_native_cutoff_energy_family g e he hei
    (isCompact_closedBall (0:E) R₀) hsource hκ0 hκ1 p hp ht χout hχout W₀.outer_compact
    W₀.outer_support W₀.outer_plateau S O hO
  obtain ⟨dC,Ccore,hdC,hCcore,hCore⟩:=exists_nativeHomogeneous_uniform_core_energy g hY gE e he hei
    hR₀ hsource hcoeff hB hρ χin hχin W₀.inner_compact W₀.inner_support W₀.inner_plateau
  let δ:=min d₀ (min dC (min 1 (R₀/(2*H))))
  let CT:=(Cbase+CR*CY)*‖T₀‖
  let CQ:=CM*CY*‖T₀‖
  let C:=C₀+CQ+(Ccore+1)*CT
  have hCM₀:0 ≤ CM:=by
    have hn:0 ≤ CM*Real.sqrt (d₀/2):=(norm_nonneg W₀.Q).trans W₀.native_field_bound
    nlinarith [Real.sqrt_pos.2 (show 0 < d₀/2 by linarith)]
  have hCR₀:0 ≤ CR:=by
    have hn:0 ≤ CR*Real.sqrt (d₀/2):=(norm_nonneg W₀.R).trans W₀.return_bound
    nlinarith [Real.sqrt_pos.2 (show 0 < d₀/2 by linarith)]
  have hCT:0 ≤ CT:=by dsimp only [CT];positivity
  have hCQ:0 ≤ CQ:=by dsimp only [CQ];positivity
  have hC:0 ≤ C:=by dsimp only [C];positivity
  have hδ:0 < δ:=by dsimp only [δ];positivity
  refine ⟨cTail,m,n,b,S,δ,CR,CM,C,N,CI,Ccore,Cbase,CY,χin,χout,hχin,hχout,O,T₀,L₀,hN,hCI,hCcore,hCbase,hCY,hEnergyReceiver,hTailBound,hmL,hSComp,hδ,hC,hModel,fun a ha had=>?_⟩
  obtain ⟨ha1,W,hI,Rbase,hRb,hRF,hYC,hFix⟩:=hStage a ha (had.trans (min_le_left _ _))
  have haC:a ≤ dC:=had.trans ((min_le_right _ _).trans (min_le_left _ _))
  have haH:a ≤ R₀/(2*H):=had.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hfit:euclideanDilatedDomain a O⊆closedBall (0:E) R₀:=by
    apply euclideanDilatedBall_subset_closedBall ha
    have hh:a*(2*H) ≤ R₀:=(le_div_iff₀ (by positivity:0 < 2*H)).mp haH
    nlinarith [mul_nonneg ha.le hH.le]
  obtain ⟨Q₀,hQ₀,hQ₀v⟩:=hLift a ha ha1 hfit
  obtain ⟨ha1',hfit3,hΩ,Qcore,hQcore,hQeq⟩:=hCore a ha haC
  let Ψ:=nativeChartScaledCutoffTest g e hei ha χin hχin W₀.inner_compact (ball (0:E) 3) W₀.inner_support hfit3
  have hcEq:W.core=Ψ:=by apply Subtype.ext;exact W.core_coordinate
  have hMult (R:nativeHomogeneousEnergySpace g (fun _:M=>0) contMDiff_const (e '' ball (0:E) (a*64))):
      ‖energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth R.val‖ ≤ Ccore*‖R‖:=by
    rw [hcEq,←hQeq R]
    exact Qcore.le_of_opNorm_le hQcore R
  let Y:=nativeOriginalAffineFeedbackCLM W (nativeActualH4BaselineResidualCLM W) Rbase
  let Rtot:=nativeOriginalAffineReturnCLM W (nativeActualH4BaselineResidualCLM W) Rbase
  refine ⟨ha1,W,hI,hMult,Rbase,Q₀,hRb,hYC,hRF,hQ₀v,?_,hFix⟩
  apply (nativeOriginalSignedEnergyCLM W T₀ Q₀ Rbase).opNorm_le_bound (by positivity)
  intro f
  have hTf:‖T₀ f‖ ≤ ‖T₀‖*‖f‖:=T₀.le_opNorm f
  have hYf:‖Y (T₀ f)‖ ≤ CY*(‖T₀‖*‖f‖):=
    (Y.le_of_opNorm_le hYC _).trans (mul_le_mul_of_nonneg_left hTf hCY)
  have hRf:‖Rtot (T₀ f)‖ ≤ CT*Real.sqrt a*‖f‖:=by
    change ‖Rbase (T₀ f)+W.R (Y (T₀ f))‖ ≤ _
    apply (norm_add_le _ _).trans
    have hb₀:‖Rbase (T₀ f)‖ ≤ (Cbase*Real.sqrt a)*(‖T₀‖*‖f‖):=
      (Rbase.le_of_opNorm_le hRb _).trans (mul_le_mul_of_nonneg_left hTf (by positivity))
    have hr:‖W.R (Y (T₀ f))‖ ≤ (CR*Real.sqrt a)*(CY*(‖T₀‖*‖f‖)):=
      (W.R.le_of_opNorm_le W.return_bound _).trans (mul_le_mul_of_nonneg_left hYf (by positivity))
    exact (add_le_add hb₀ hr).trans_eq (by dsimp only [CT];ring)
  have hQf:‖W.Q (Y (T₀ f)).val‖ ≤ CQ*Real.sqrt a*‖f‖:=
    ((W.Q.le_of_opNorm_le W.native_field_bound _).trans
      (mul_le_mul_of_nonneg_left hYf (by positivity))).trans_eq (by dsimp only [CQ];ring)
  have hMf:‖energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth (Rtot (T₀ f)).val‖ ≤
      Ccore*(CT*Real.sqrt a*‖f‖):=(hMult _).trans (mul_le_mul_of_nonneg_left hRf hCcore)
  change ‖Q₀ f+W.Q (Y (T₀ f)).val+
    energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) W.core W.core.smooth (Rtot (T₀ f)).val-
    (Rtot (T₀ f)).val‖ ≤ _
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans
  exact (add_le_add (add_le_add (add_le_add (Q₀.le_of_opNorm_le hQ₀ f) hQf) hMf) hRf).trans_eq
    (by dsimp only [C];ring)

#print axioms exists_nativeOriginal_signed_energy_trace_producer
end Yamabe3.Analysis.SpherePolar
