import Yamabe3.Analysis.NativeTwoSidedGlobalFeedback
import Yamabe3.Analysis.NativeMatchedJacobianRowBound
import Yamabe3.Analysis.NativePhysicalSourceDuality
import Yamabe3.Analysis.NativePhysicalTestUniqueness

/-! The same global feedback pair yields an actual L2 physical operator
on the punctured ball equal to the original source, via every compact
physical test. The source and shell weights retain their normalization. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
attribute [local irreducible] nativeFullShellSourceReturnCLM nativeTwoSidedJacobianRowCLM
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1) (t₀ : ℝ)

def nativeTwoSidedPhysicalJacobian (g : RiemannianMetric 3 E) (ε : ℝ) (X : NativeTwoSidedSource) : E→ℝ :=
  nativePhysicalShellAssembly (fun n => nativeTwoSidedJacobianRowCLM P hp v hv hb t₀ g ε (nativeLogShellCenter n) X)

theorem exists_nativeTwoSidedJacobianRow_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃C : ℝ,0<C ∧ ∀ ε : ℝ,0≤ε → ε≤1 → ∀ a∈Λ,∀ s : ℝ,0 ≤ s → ∀ X : NativeTwoSidedSource,
      ‖nativeTwoSidedJacobianRowCLM P hp v hv hb t₀ (g a) ε s X‖≤C*‖X‖ := by
  obtain ⟨D,hD,hd⟩ := exists_nativeTwoSidedAllScale_bound P hp v hv hb t₀
  obtain ⟨H,hH,hh⟩ := exists_nativeTwoSidedGeometricRow_decay P hp v hv hb t₀ Λ g hB hρ
  let C := (3+‖P.potential‖*Real.exp 1)*D+H
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,fun ε hε hε1 a ha s hs X => ?_⟩
  let J := nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X
  let V := boundedTimeTranslate ℝ s P.potential
  have hJ := (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s).le_of_opNorm_le (hd s) X
  have hf := (nativeFlatCollarJet_norm_bound V J).trans (mul_le_mul_of_nonneg_left hJ (by positivity : 0≤3+‖V‖*Real.exp 1))
  have hn : ‖V‖=‖P.potential‖ := boundedTimeTranslate_norm ℝ s P.potential
  rw [hn] at hf
  have he := (nativeTwoSidedGeometricRowCLM P hp v hv hb t₀ (g a) ε s).le_of_opNorm_le (hh ε hε hε1 a ha s hs) X
  have hs' : Real.exp (-s)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
  have hs'' : H*ε*Real.exp (-s)≤H :=
    (mul_le_of_le_one_right (mul_nonneg hH.le hε) hs').trans (mul_le_of_le_one_right hH.le hε1)
  have he' := he.trans (mul_le_mul_of_nonneg_right hs'' (norm_nonneg X))
  unfold nativeTwoSidedJacobianRowCLM
  change ‖nativeFlatCollarJetCLM V J+nativeTwoSidedGeometricRowCLM P hp v hv hb t₀ (g a) ε s X‖≤_
  exact (norm_add_le _ _).trans ((add_le_add hf he').trans_eq (by dsimp only [C];ring))

variable {t₀} (ht : 0<t₀)

theorem nativeTwoSidedGlobal_fixed_physical_ae
    (hpot : P.potential=delaunayPhasePotentialBCF v hv hb 0)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (X Y : NativeTwoSidedSource) (hY : Y=X+nativeTwoSidedGlobalSourceCLM P hp v hv hb ht (g a) ε Y) :
    MemLp (nativeTwoSidedPhysicalJacobian P hp v hv hb t₀ (g a) ε Y) 2
      (volume.restrict (Metric.ball 0 1 \ {(0:E)})) ∧
    nativeTwoSidedPhysicalJacobian P hp v hv hb t₀ (g a) ε Y=ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})]
      (fun x => -nativeFullPhysicalSourceRepresentative X.1 x) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeTwoSidedJacobianRow_bound P hp v hv hb t₀ Λ g hB hρ
  let U (n : ℕ) := nativeTwoSidedJacobianRowCLM P hp v hv hb t₀ (g a) ε (nativeLogShellCenter n) Y
  have hU (n : ℕ) : ‖U n‖≤C*‖Y‖ := hc ε hε hε1 a ha (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n) Y
  have hCY : 0≤C*‖Y‖ := mul_nonneg hC.le (norm_nonneg Y)
  have hm := nativePhysicalShellAssembly_memLp U hCY hU
  refine ⟨hm,?_⟩
  apply nativePhysicalTest_ae_eq_negative hm (nativeFullPhysicalSource_memLp X.1)
  intro φ hφ hcs hs
  have h0 : (0:E)∉tsupport φ := fun h => (hs h).2 (by simp)
  let G := nativePhysicalPairTestL2 φ hφ hcs h0
  have hsum := nativeTwoSidedGlobal_fixed_pairing P hp v hv hb ht hpot Λ g hB hρ ε hε hε1 a ha X Y hY
    G (nativePhysicalPairTestL2_positive φ hφ hcs h0 hs)
  have hsrc := nativeFullPhysicalSource_physical_test_pairing_on_ball X.1 φ hφ hcs h0 hs
  change HasSum _ (-inner ℝ X.1 (nativePhysicalPairTestL2 φ hφ hcs h0)) at hsum
  rw [hsrc.2] at hsum
  have ht : HasSum (fun n => Real.exp (-5*nativeLogShellCenter n/2)*
      (∫x in nativeSourceShell,(U n : E→ℝ) x*φ (Real.exp (-nativeLogShellCenter n) • x)))
      (-(∫x in Metric.ball 0 1 \ {(0:E)},nativeFullPhysicalSourceRepresentative X.1 x*φ x)) := by
    simpa only [G,nativeFullShellSourceReturn_physical_test] using hsum
  exact (nativePhysicalShellAssembly_test_hasSum U hCY hU φ hφ.continuous hcs).unique ht

#print axioms exists_nativeTwoSidedJacobianRow_bound
#print axioms nativeTwoSidedGlobal_fixed_physical_ae
end Yamabe3.Analysis.SpherePolar
