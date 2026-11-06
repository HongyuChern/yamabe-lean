import Yamabe3.Analysis.NativeTwoSidedGlobalEnergy
import Yamabe3.Analysis.EuclideanSupportedEnergyMultiplier

/-! The actual model field with any fixed far cutoff has a bounded
realization in the true supported domain completion. A sufficiently
large finite collar cover is proved to equal one on that cutoff's
support; no unproved global H1 or trace-kernel input is introduced. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
attribute [local instance] Classical.propDecidable
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Delaunay UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD

theorem exists_nativeOuter_energy_cover {χ:E→ℝ}
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1)) (S₀:ℝ) :
    ∃N:ℕ,∀x∈tsupport (fun y:E=>χ (Real.exp S₀ • y)),nativeOuterCollarCutoff χ (N+1) x=1 := by
  obtain ⟨N,hN⟩:=exists_nat_gt (1-4*S₀)
  refine ⟨N,fun x hx=>?_⟩
  have hm:Real.exp S₀ • x∈tsupport χ :=
    (tsupport_comp_eq_preimage χ (Homeomorph.smulOfNeZero (Real.exp S₀) (Real.exp_ne_zero _))).le hx
  have hb:=mem_ball_zero_iff.mp (hs hm)
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hb
  have hn:‖Real.exp (-((N+1:ℕ):ℝ)/4) • x‖ ≤ Real.exp (-(1/8:ℝ)) := by
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    have he:Real.exp (-((N+1:ℕ):ℝ)/4)*‖x‖=
        Real.exp (-((N+1:ℕ):ℝ)/4-S₀)*(Real.exp S₀*‖x‖) := by
      rw [←mul_assoc,←Real.exp_add]
      congr 2
      ring
    rw [he]
    apply ((mul_lt_mul_of_pos_left hb (Real.exp_pos _)).trans_le ?_).le
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  exact (h1 _ (by simpa only [mem_closedBall,dist_zero_right] using hn)).self_of_nhds

theorem exists_nativeTwoSided_cutoff_energy_family
    (P:NativeHighPotential)
    (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (v:ℝ→ℝ) (hv:Continuous v) (hb:∀t,0 ≤ v t ∧ v t ≤ 1) (b:ℝ) {τ:ℝ} (ht:0 < τ)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆ball (0:E) (Real.exp (1/8:ℝ)))
    (h1:∀x∈closedBall (0:E) (Real.exp (-(1/8:ℝ))),χ=ᶠ[𝓝 x](fun _=>1))
    (S₀:ℝ) (O:Set E) (hO:tsupport (fun y:E=>χ (Real.exp S₀ • y))⊆O) :
    ∃L:NativeTwoSidedSource →L[ℝ] H1Zero Deuc O,
      ∀X:NativeTwoSidedSource,∃wi wo:ℝ×S→ℝ,Measurable wi ∧ Measurable wo ∧
        (∀s:ℝ,NativeScaledJetRep (nativeTwoSidedAllScaleJetCLM P hp v hv hb τ s X) s wi) ∧
        (∀s:ℝ,NativeScaledJetRep (nativeSupportedTwoSidedExteriorAllScaleJet P hp v hv hb b ht X s) s wo) ∧
        (toL2 Deuc O (L X):E→ℝ)=ᵐ[volume]
          fun y=>χ (Real.exp S₀ • y)*(ball (0:E) 1).piecewise (cylinderLift wi) (cylinderLift wo) y := by
  let φ:E→ℝ:=fun y=>χ (Real.exp S₀ • y)
  have hφ:ContDiff ℝ ∞ φ:=hχ.comp (contDiff_id.const_smul _)
  have hcφ:HasCompactSupport φ:=hc.comp_homeomorph (Homeomorph.smulOfNeZero (Real.exp S₀) (Real.exp_ne_zero _))
  obtain ⟨N,hN⟩:=exists_nativeOuter_energy_cover hs h1 S₀
  obtain ⟨L,hL⟩:=exists_nativeTwoSided_global_energy_family P hp v hv hb b ht χ hχ hc hs h1 N
  let M:=euclideanSupportedEnergyMulCLM O φ hφ hcφ hO
  refine ⟨M.comp L,fun X=>?_⟩
  obtain ⟨wi,wo,hwi,hwo,hi,ho,hE⟩:=hL X
  refine ⟨wi,wo,hwi,hwo,hi,ho,?_⟩
  have hM:=euclideanSupportedEnergyMulCLM_ae O φ hφ hcφ hO (L X)
  filter_upwards [hM,hE] with y hm he
  change toL2 Deuc O (M (L X)) y=_
  rw [hm,he]
  by_cases hy:φ y=0
  · change φ y*_=φ y*_
    rw [hy,zero_mul,zero_mul]
  · have ht:y∈tsupport φ:=subset_tsupport φ (Function.mem_support.mpr hy)
    rw [hN y ht,one_mul]

#print axioms exists_nativeOuter_energy_cover
#print axioms exists_nativeTwoSided_cutoff_energy_family
end Yamabe3.Analysis.SpherePolar
