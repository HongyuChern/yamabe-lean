import Yamabe3.Analysis.NativeMatchedGeometricRows
import Yamabe3.Analysis.NativeFullShellReturn
import Yamabe3.Analysis.NativeLogShellPartition

/-! Norm-convergent full-mode source feedback of the actual geometric
error. The shell return has no discarded low component. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (B : NativeHighPotential) (p : DelaunayPhaseData κ)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)

def nativeMatchedGeometricSourceTerm (g : RiemannianMetric 3 E) (ε : ℝ) (n : ℕ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)).comp
    (nativeMatchedGeometricRowCLM hκ0 hκ1 B p hp g ε (nativeLogShellCenter n))

def nativeMatchedGlobalGeometricSourceCLM (g : RiemannianMetric 3 E) (ε : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] Lp AngularSpectralSpace 2 (volume : Measure ℝ) :=
  ∑' n,nativeMatchedGeometricSourceTerm hκ0 hκ1 B p hp g ε n

omit B p hp in
theorem exists_uniform_nativeMatchedGeometricSourceTerm_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀ ε : ℝ,0 ≤ ε → ε ≤ 1 → ∀ a ∈ Λ, ∀ n : ℕ,
        ‖nativeMatchedGeometricSourceTerm hκ0 hκ1 B p hp (g a) ε n‖≤C*ε*Real.exp (-nativeLogShellCenter n) := by
  obtain ⟨C,hC,hc⟩ := exists_uniform_nativeMatchedGeometricRow_decay hκ0 hκ1 Λ g hB hρ
  let L := ‖nativeL2FullPhysicalSourceCLM‖*Real.exp 1
  have hL : 0≤L := by positivity
  refine ⟨(L+1)*C,by positivity,fun B p hp ε hε hε1 a ha n => ?_⟩
  have ht := ContinuousLinearMap.opNorm_comp_le
    (nativeFullShellSourceReturnCLM (nativeLogShellCenter n))
    (nativeMatchedGeometricRowCLM hκ0 hκ1 B p hp (g a) ε (nativeLogShellCenter n))
  have hr := hc B p hp ε hε hε1 a ha (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n)
  apply ht.trans
  have hbound := mul_le_mul (nativeFullShellSourceReturn_norm (nativeLogShellCenter n)) hr
    (norm_nonneg _) hL
  apply hbound.trans
  change L*(C*ε*Real.exp (-nativeLogShellCenter n))≤_
  nlinarith [Real.exp_pos (-nativeLogShellCenter n),mul_nonneg hC.le hε]

theorem nativeMatchedGeometricSourceTerm_summable
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ) :
    Summable (nativeMatchedGeometricSourceTerm hκ0 hκ1 B p hp (g a) ε) := by
  obtain ⟨C,hC,hc⟩ := exists_uniform_nativeMatchedGeometricSourceTerm_bound hκ0 hκ1 Λ g hB hρ
  exact (nativeLogShell_decay_summable.mul_left (C*ε)).of_norm_bounded (hc B p hp ε hε hε1 a ha)

omit B p hp in
theorem exists_uniform_nativeMatchedGlobalGeometricSource_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀ ε : ℝ,0 ≤ ε → ε ≤ 1 → ∀ a ∈ Λ, 
        ‖nativeMatchedGlobalGeometricSourceCLM hκ0 hκ1 B p hp (g a) ε‖≤C*ε := by
  obtain ⟨C,hC,hc⟩ := exists_uniform_nativeMatchedGeometricSourceTerm_bound hκ0 hκ1 Λ g hB hρ
  let S := Real.exp (-(1/4:ℝ))*(1-Real.exp (-(1/2:ℝ)))⁻¹
  have hS : 0<S := by
    dsimp only [S]
    exact mul_pos (Real.exp_pos _) (inv_pos.mpr (sub_pos.mpr
      (Real.exp_lt_one_iff.mpr (by norm_num))))
  refine ⟨C*S,by positivity,fun B p hp ε hε hε1 a ha => ?_⟩
  have hbound := tsum_of_norm_bounded
    ((nativeLogShell_decay_summable.hasSum).mul_left (C*ε)) (hc B p hp ε hε hε1 a ha)
  rw [nativeLogShell_decay_sum] at hbound
  exact hbound.trans_eq (by dsimp only [S];ring)

#print axioms exists_uniform_nativeMatchedGeometricSourceTerm_bound
#print axioms nativeMatchedGeometricSourceTerm_summable
#print axioms exists_uniform_nativeMatchedGlobalGeometricSource_bound
end Yamabe3.Analysis.SpherePolar
