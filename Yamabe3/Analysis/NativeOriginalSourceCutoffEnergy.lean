import Yamabe3.Analysis.NativeOriginalSourceGlobalEnergy
import Yamabe3.Analysis.NativeOuterEnergyCutoff

/-! The same original-source matched field with ANY prescribed far
cutoff has a bounded realization in the TRUE supported H1 completion.
The original weighted H2 forcing stays in its original source space. -/
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

theorem exists_originalSource_matched_cutoff_energy
    {κ:ℝ} (hκ0:0 ≤ κ) (hκ1:κ < 1) (p:DelaunayPhaseData κ)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|) ≤ κ)
    {τ:ℝ} (ht:0 < τ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    (S₀:ℝ) (O:Set E) (hO:tsupport (fun y:E=>χ (Real.exp S₀ • y))⊆O) :
    let P:=p.nativeHighPotential hκ0 hκ1
    ∃(T:HalfEndPhysicalH2SourceGraph →L[ℝ] HalfEndPhysicalH4Graph)
      (L:HalfEndPhysicalH2SourceGraph →L[ℝ] H1Zero Deuc O),
      ∀f:HalfEndPhysicalH2SourceGraph,∃F:E→ℝ,∃hF2:ContDiffOn ℝ 2 F ({0}ᶜ:Set E),
        EqOn (nativeH4GraphFunction (T f)) F (closedBall (0:E) 4) ∧
        (F=ᵐ[volume.restrict (ball (0:E) 1\{0})]fullModelPhysicalField hκ0 hκ1 p f) ∧
        ∃qi wo:ℝ×SpherePolar.S→ℝ,Measurable qi ∧ Measurable wo ∧
          (∀i:HalfEndPhysicalSliceIndex,
            ((nativeH4MatchedScaleJetCLM (fullBubbleHighPotential (-τ)) P hp i (T f)).val.1:E→ℝ)
              =ᵐ[volume.restrict nativePoissonEntranceCollar]
                fun x=>Real.exp (3*i.val/2)*(F (Real.exp (-i.val) • x)+cylinderLift qi (Real.exp (-i.val) • x))) ∧
          (∀s:ℝ,NativeScaledJetRep (nativeH4MatchedExteriorAllScaleJet P ht (T f) s) s wo) ∧
          (toL2 Deuc O (L f):E→ℝ)=ᵐ[volume]
            fun y=>χ (Real.exp S₀ • y)*(ball (0:E) 1).piecewise (fun x=>F x+cylinderLift qi x) (cylinderLift wo) y := by
  dsimp only
  let φ:E→ℝ:=fun y=>χ (Real.exp S₀ • y)
  have hφ:ContDiff ℝ ∞ φ:=hχ.comp (contDiff_id.const_smul _)
  have hcφ:HasCompactSupport φ:=hc.comp_homeomorph (Homeomorph.smulOfNeZero (Real.exp S₀) (Real.exp_ne_zero _))
  obtain ⟨N,hN⟩:=exists_nativeOuter_energy_cover hs h1 S₀
  obtain ⟨T,L,hL⟩:=exists_originalSource_matched_global_energy hκ0 hκ1 p hp ht χ hχ hc hs h1 N
  let M:=euclideanSupportedEnergyMulCLM O φ hφ hcφ hO
  refine ⟨T,M.comp L,fun f=>?_⟩
  obtain ⟨F,hF2,hF,hFAE,qi,wo,hqi,hwo,hi,ho,hE⟩:=hL f
  refine ⟨F,hF2,hF,hFAE,qi,wo,hqi,hwo,hi,ho,?_⟩
  have hM:=euclideanSupportedEnergyMulCLM_ae O φ hφ hcφ hO (L f)
  filter_upwards [hM,hE] with y hm he
  change toL2 Deuc O (M (L f)) y=_
  rw [hm,he]
  by_cases hy:φ y=0
  · change φ y*_=φ y*_
    rw [hy,zero_mul,zero_mul]
  · have ht:y∈tsupport φ:=subset_tsupport φ (Function.mem_support.mpr hy)
    rw [hN y ht,one_mul]

#print axioms exists_originalSource_matched_cutoff_energy
end Yamabe3.Analysis.UniformElliptic
