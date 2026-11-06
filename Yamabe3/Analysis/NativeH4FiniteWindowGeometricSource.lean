import Yamabe3.Analysis.NativeH4MatchedExteriorAllScale
import Yamabe3.Analysis.NativeH4MatchedGlobalSource
import Yamabe3.Analysis.NativeFiniteOuterWindowSource


/-! The original H4 baseline produces the ACTUAL full inner and finite
outer geometric residual. Only that residual enters whole-time L2;
the original weighted source itself is not assumed L2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
variable (P:NativeHighPotential)
  (hp:∀t,(∫s:ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
  {τ:ℝ} (ht:0 < τ)

private def modelBound:ℝ := (exists_nativeH4MatchedExteriorAllScale_bound P ht).choose
private theorem modelBound_nonneg:0 ≤ modelBound P ht :=
  (exists_nativeH4MatchedExteriorAllScale_bound P ht).choose_spec.1
private def modelJet (s:ℝ) (hs:s ≤ 0):HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure :=
  ((exists_nativeH4MatchedExteriorAllScale_bound P ht).choose_spec.2 s hs).choose
private theorem modelJet_bound (s:ℝ) (hs:s ≤ 0):‖modelJet P ht s hs‖ ≤ modelBound P ht :=
  ((exists_nativeH4MatchedExteriorAllScale_bound P ht).choose_spec.2 s hs).choose_spec.1

private theorem outerCenter_nonpos (n:ℕ):nativeOuterLogShellCenter n ≤ 0 := by
  unfold nativeOuterLogShellCenter
  have hn:(0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

def nativeH4FiniteWindowGeometricRowCLM (g:RiemannianMetric 3 E) (ε:ℝ) (n:ℕ) :
    HalfEndPhysicalH4Graph →L[ℝ] NativeCollarL2 :=
  (nativeBCFCollarErrorCLM g (ε*Real.exp (-nativeOuterLogShellCenter n))
    (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ))).comp
      (nativeCollarJetClosure.subtypeL.comp
        (modelJet P ht (nativeOuterLogShellCenter n) (outerCenter_nonpos n)))

def nativeH4FiniteWindowGlobalSourceCLM (m:ℕ) (g:RiemannianMetric 3 E) (ε:ℝ) :
    HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource :=
  (nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp g ε).prod
    (nativeFiniteOuterWindowSourceCLM m (fun i=> nativeH4FiniteWindowGeometricRowCLM P ht g ε i))

theorem nativeH4FiniteWindowGeometricRow_same_field (g:RiemannianMetric 3 E) (ε:ℝ) (n:ℕ) (X:HalfEndPhysicalH4Graph) :
    nativeH4FiniteWindowGeometricRowCLM P ht g ε n X=
      nativeBCFCollarErrorCLM g (ε*Real.exp (-nativeOuterLogShellCenter n))
        (boundedTimeTranslate ℝ (nativeOuterLogShellCenter n) (fullBubblePhasePotential τ))
        (nativeH4MatchedExteriorAllScaleJet P ht X (nativeOuterLogShellCenter n)).val := by
  change nativeBCFCollarErrorCLM g _ _ (modelJet P ht _ _ X).val=_
  dsimp only [modelJet]
  rw [((exists_nativeH4MatchedExteriorAllScale_bound P ht).choose_spec.2
    (nativeOuterLogShellCenter n) (outerCenter_nonpos n)).choose_spec.2 X]

theorem exists_nativeH4FiniteWindowGlobalSource_bound
    (m:ℕ) {ι:Type*} (Λ:Finset ι) (g:ι→RiemannianMetric 3 E)
    (hB:∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ:∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃δ C:ℝ,0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ε:ℝ,0 ≤ ε → ε ≤ δ → ∀p∈Λ,
      ‖nativeH4FiniteWindowGlobalSourceCLM P hp ht m (g p) ε‖ ≤ C*ε := by
  obtain ⟨CG,hCG,hg⟩:=exists_native_bcf_full_collar_error_linear_bound Λ g hB hρ (norm_nonneg (fullBubblePhasePotential τ))
  obtain ⟨CI,hCI,hi⟩:=exists_nativeH4MatchedInnerGlobalSource_bound (fullBubbleHighPotential (-τ)) P hp Λ g hB hρ
  let M:=modelBound P ht
  have hM:0 ≤ M := modelBound_nonneg P ht
  let L:=‖nativeL2FullPhysicalSourceCLM‖*Real.exp 1
  have hL:0 ≤ L := by dsimp only [L];positivity
  let CO:=L*(m:ℝ)*CG*M*Real.exp ((m:ℝ)/2)
  have hCO:0 ≤ CO := by dsimp only [CO];positivity
  let δ:=min 1 (Real.exp (-(m:ℝ)/2))
  refine ⟨δ,1+CI+CO,lt_min zero_lt_one (Real.exp_pos _),min_le_left _ _,by positivity,?_⟩
  intro ε hε hεδ p hp'
  have hε1:ε ≤ 1 := hεδ.trans (min_le_left _ _)
  have hrows (i:Fin m):‖nativeH4FiniteWindowGeometricRowCLM P ht (g p) ε i‖ ≤ (CG*M*Real.exp ((m:ℝ)/2))*ε := by
    let s:=nativeOuterLogShellCenter i
    have hsm:-s ≤ (m:ℝ)/2 := by
      have hn:(i.val:ℝ)+1 ≤ m := by exact_mod_cast i.isLt
      dsimp only [s,nativeOuterLogShellCenter]
      linarith
    have hex:Real.exp (-s) ≤ Real.exp ((m:ℝ)/2) := Real.exp_le_exp.mpr hsm
    have hr1:ε*Real.exp (-s) ≤ 1 := by
      apply (mul_le_mul (hεδ.trans (min_le_right _ _)) hex (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
      rw [←Real.exp_add,show -(m:ℝ)/2+(m:ℝ)/2=0 by ring,Real.exp_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro X
    have hh:=hg (ε*Real.exp (-s)) (by positivity) hr1 p hp'
      (boundedTimeTranslate ℝ s (fullBubblePhasePotential τ))
      (boundedTimeTranslate_norm ℝ s (fullBubblePhasePotential τ)).le
      (modelJet P ht s (outerCenter_nonpos i) X).val
    have hmodel:‖modelJet P ht s (outerCenter_nonpos i) X‖ ≤ M*‖X‖ :=
      (modelJet P ht s (outerCenter_nonpos i)).le_of_opNorm_le
        (modelJet_bound P ht s (outerCenter_nonpos i)) X
    change ‖nativeH4FiniteWindowGeometricRowCLM P ht (g p) ε i X‖ ≤ (CG*(ε*Real.exp (-s)))*‖modelJet P ht s (outerCenter_nonpos i) X‖ at hh
    calc
      _ ≤ (CG*(ε*Real.exp (-s)))*(M*‖X‖) :=
        hh.trans (mul_le_mul_of_nonneg_left hmodel (by positivity))
      _ = (CG*ε*M*‖X‖)*Real.exp (-s) := by ring
      _ ≤ (CG*ε*M*‖X‖)*Real.exp ((m:ℝ)/2) :=
        mul_le_mul_of_nonneg_left hex (by positivity)
      _ = _ := by ring
  have houter:‖nativeFiniteOuterWindowSourceCLM m
      (fun i=> nativeH4FiniteWindowGeometricRowCLM P ht (g p) ε i)‖ ≤ CO*ε := by
    apply (nativeFiniteOuterWindowSource_norm m _).trans
    apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=> hrows i)) hL).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp only [CO,L]
    ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro X
  change ‖(nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g p) ε X,
    nativeFiniteOuterWindowSourceCLM m (fun i=> nativeH4FiniteWindowGeometricRowCLM P ht (g p) ε i) X)‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · exact ((nativeH4MatchedInnerGlobalSourceCLM (fullBubbleHighPotential (-τ)) P hp (g p) ε).le_of_opNorm_le
      (hi ε hε hε1 p hp') X).trans
      (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCO hε]) (norm_nonneg X))
  · exact ((nativeFiniteOuterWindowSourceCLM m (fun i=> nativeH4FiniteWindowGeometricRowCLM P ht (g p) ε i)).le_of_opNorm_le houter X).trans
      (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCI.le hε]) (norm_nonneg X))

#print axioms nativeH4FiniteWindowGeometricRow_same_field
#print axioms exists_nativeH4FiniteWindowGlobalSource_bound
end Yamabe3.Analysis.UniformElliptic
