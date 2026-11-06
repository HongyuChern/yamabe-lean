import Yamabe3.Analysis.NativeH4MatchedAllScale
import Yamabe3.Analysis.NativeTwoSidedGlobalSource

/-! The original H4 source field with the same coupled boundary correction
has a genuine full-mode geometric residual in the whole-line L2 source
space. Only this decaying error is transferred to L2; the original source
is never assumed to belong to L2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Yamabe3.Analysis.Delaunay
variable (B P : NativeHighPotential)
  (hp : ∀ t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

def nativeH4NonnegativeScaleIndex (s : ℝ) (hs : 0 ≤ s) : HalfEndPhysicalSliceIndex :=
  ⟨s,le_trans (neg_nonpos.mpr (Real.log_nonneg (by norm_num))) hs⟩

def nativeH4MatchedGeometricRowCLM (g : RiemannianMetric 3 E) (ε s : ℝ) (hs : 0 ≤ s) :
    HalfEndPhysicalH4Graph →L[ℝ] NativeCollarL2 :=
  (nativeBCFCollarErrorCLM g (ε*Real.exp (-s)) (boundedTimeTranslate ℝ s P.potential)).comp
    (nativeH4MatchedScaleRawJetCLM B P hp (nativeH4NonnegativeScaleIndex s hs))

def nativeH4MatchedGeometricSourceTerm (g : RiemannianMetric 3 E) (ε : ℝ) (n : ℕ) :
    HalfEndPhysicalH4Graph →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)).comp
    (nativeH4MatchedGeometricRowCLM B P hp g ε (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n))

def nativeH4MatchedInnerGlobalSourceCLM (g : RiemannianMetric 3 E) (ε : ℝ) :
    HalfEndPhysicalH4Graph →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  ∑'n,nativeH4MatchedGeometricSourceTerm B P hp g ε n

theorem exists_nativeH4MatchedGeometricRow_decay
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0≤ε → ε≤1 → ∀ a ∈ Λ, ∀ (s : ℝ) (hs : 0 ≤ s),
      ‖nativeH4MatchedGeometricRowCLM B P hp (g a) ε s hs‖≤C*ε*Real.exp (-s) := by
  obtain ⟨C,hC,hc⟩ := exists_native_bcf_full_collar_error_linear_bound Λ g hB hρ (norm_nonneg P.potential)
  obtain ⟨D,hD,hd⟩ := exists_nativeH4MatchedScale_bound B P hp
  refine ⟨C*D,by positivity,fun ε hε hε1 a ha s hs => ?_⟩
  have he : Real.exp (-s)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro X
  have h := hc (ε*Real.exp (-s)) (by positivity) ((mul_le_of_le_one_right hε he).trans hε1)
    a ha (boundedTimeTranslate ℝ s P.potential) (boundedTimeTranslate_norm ℝ s P.potential).le
    (nativeH4MatchedScaleRawJetCLM B P hp (nativeH4NonnegativeScaleIndex s hs) X)
  have hj := (nativeH4MatchedScaleRawJetCLM B P hp (nativeH4NonnegativeScaleIndex s hs)).le_of_opNorm_le (hd (nativeH4NonnegativeScaleIndex s hs)) X
  exact (h.trans (mul_le_mul_of_nonneg_left hj (by positivity))).trans_eq (by ring)

theorem exists_nativeH4MatchedGeometricSourceTerm_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0≤ε → ε≤1 → ∀ a ∈ Λ, ∀ n : ℕ,
      ‖nativeH4MatchedGeometricSourceTerm B P hp (g a) ε n‖≤C*ε*Real.exp (-nativeLogShellCenter n) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeH4MatchedGeometricRow_decay B P hp Λ g hB hρ
  let L := ‖nativeL2FullPhysicalSourceCLM‖*Real.exp 1
  have hL : 0≤L := by positivity
  refine ⟨(L+1)*C,by positivity,fun ε hε hε1 a ha n => ?_⟩
  have ht := ContinuousLinearMap.opNorm_comp_le (nativeFullShellSourceReturnCLM (nativeLogShellCenter n))
    (nativeH4MatchedGeometricRowCLM B P hp (g a) ε (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n))
  have hr := hc ε hε hε1 a ha (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n)
  apply ht.trans
  apply (mul_le_mul (nativeFullShellSourceReturn_norm (nativeLogShellCenter n)) hr (norm_nonneg _) hL).trans
  change L*(C*ε*Real.exp (-nativeLogShellCenter n))≤_
  nlinarith [Real.exp_pos (-nativeLogShellCenter n),mul_nonneg hC.le hε]

theorem nativeH4MatchedGeometricSourceTerm_summable
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ) :
    Summable (nativeH4MatchedGeometricSourceTerm B P hp (g a) ε) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeH4MatchedGeometricSourceTerm_bound B P hp Λ g hB hρ
  exact (nativeLogShell_decay_summable.mul_left (C*ε)).of_norm_bounded (hc ε hε hε1 a ha)

theorem exists_nativeH4MatchedInnerGlobalSource_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ ε : ℝ,0≤ε → ε≤1 → ∀ a ∈ Λ, 
      ‖nativeH4MatchedInnerGlobalSourceCLM B P hp (g a) ε‖≤C*ε := by
  obtain ⟨C,hC,hc⟩ := exists_nativeH4MatchedGeometricSourceTerm_bound B P hp Λ g hB hρ
  let S := Real.exp (-(1/4:ℝ))*(1-Real.exp (-(1/2:ℝ)))⁻¹
  have hS : 0<S := by
    dsimp only [S]
    exact mul_pos (Real.exp_pos _) (inv_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))))
  refine ⟨C*S,by positivity,fun ε hε hε1 a ha => ?_⟩
  have h := tsum_of_norm_bounded ((nativeLogShell_decay_summable.hasSum).mul_left (C*ε)) (hc ε hε hε1 a ha)
  rw [nativeLogShell_decay_sum] at h
  exact h.trans_eq (by dsimp only [S];ring)

#print axioms exists_nativeH4MatchedGeometricRow_decay
#print axioms exists_nativeH4MatchedGeometricSourceTerm_bound
#print axioms nativeH4MatchedGeometricSourceTerm_summable
#print axioms exists_nativeH4MatchedInnerGlobalSource_bound
end Yamabe3.Analysis.UniformElliptic
