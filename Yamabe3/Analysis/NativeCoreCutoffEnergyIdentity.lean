import Yamabe3.Analysis.NativeFeedbackCorrectedEnergy
import Yamabe3.Analysis.NativeCompletedChartSameFunction
import Yamabe3.Analysis.SupportMultiplierAe

/-! The scaled/chart energy realization of a genuine local model
representative equals the native core multiplier of the SAME original
H1 field. All comparisons use native volume and completion injectivity;
there is no point evaluation on arbitrary L2 data or sphere restriction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeChartScaledCutoffTest_support
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a:ℝ} (ha:0 < a) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (O:Set E) (hs:tsupport χ⊆O) (hfit:euclideanDilatedDomain a O⊆e.source) :
    tsupport (nativeChartScaledCutoffTest g e hei ha χ hχ hc O hs hfit:M→ℝ)⊆e '' euclideanDilatedDomain a O :=
  (nativeWeakChartTest g e hei hfit (euclideanDilatedTest ha O (⟨χ,hχ.contMDiff,hc,hs⟩:EnergyTest Deuc O))).support_subset

theorem nativeCoreCutoff_completed_identity
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source)
    {a:ℝ} (ha:0 < a) (ha1:a ≤ 1) (O:Set E)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ) (hs:tsupport χ⊆O)
    (hfit:euclideanDilatedDomain a O⊆K)
    (Ω:Set M) (hΩ:IsOpen Ω) (hImage:e '' euclideanDilatedDomain a O⊆Ω)
    (z:H1Zero Deuc O) (F:E→ℝ)
    (hz:(toL2 Deuc O z:E→ℝ)=ᵐ[volume]fun x=>χ x*F x)
    (W:H1Zero g.leviCivitaData univ) (U:M→ℝ)
    (hU:U=ᵐ[g.volumeMeasure.restrict Ω](toL2 g.leviCivitaData univ W:M→ℝ))
    (hF:∀x∈tsupport χ,F x=U (e (a • x))) :
    nativeEuclideanCompletedChartScaleCLM g e he hei hK hKs ha ha1 O hfit z=
      let Ψ:=nativeChartScaledCutoffTest g e hei ha χ hχ hc O hs (hfit.trans hKs)
      energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) Ψ Ψ.smooth W := by
  dsimp only
  let Ψ:=nativeChartScaledCutoffTest g e hei ha χ hχ hc O hs (hfit.trans hKs)
  have hΨ:(Ψ:M→ℝ)=coordinateExtension e (fun x:E=>χ (a⁻¹ • x)):=rfl
  have hpoint (y:M):nativeCompactChartFunction e K (fun x:E=>χ (a⁻¹ • x)*F (a⁻¹ • x)) y=Ψ y*U y := by
    rw [hΨ]
    by_cases hy:y∈e.target
    · rw [nativeCompactChartFunction,coordinateExtension_apply e _ hy,coordinateExtension_apply e _ hy]
      by_cases hz:χ (a⁻¹ • e.symm y)=0
      · by_cases hk:e.symm y∈K <;> simp [hk,hz]
      · have ht:a⁻¹ • e.symm y∈tsupport χ:=subset_tsupport χ (Function.mem_support.mpr hz)
        have hx:e.symm y∈euclideanDilatedDomain a O:=hs ht
        rw [indicator_of_mem (hfit hx),hF _ ht,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,e.right_inv hy]
    · simp only [nativeCompactChartFunction,coordinateExtension,indicator_of_notMem hy,zero_mul]
  have hsΨ:tsupport (Ψ:M→ℝ)⊆Ω:=
    (nativeChartScaledCutoffTest_support g e hei ha χ hχ hc O hs (hfit.trans hKs)).trans hImage
  have hprod:=supported_mul_ae_of_restrict hΩ.measurableSet (Ψ:M→ℝ) hsΨ hU
  have hQ:(toL2 g.leviCivitaData univ (nativeEuclideanCompletedChartScaleCLM g e he hei hK hKs ha ha1 O hfit z):M→ℝ)
      =ᵐ[g.volumeMeasure]nativeCompactChartFunction e K (fun x:E=>χ (a⁻¹ • x)*F (a⁻¹ • x)) := by
    rw [nativeEuclideanCompletedChartScaleCLM_toL2]
    exact nativeCompletedChartL2_same_function g e he hei hK hKs ha ha1 z (fun x=>χ x*F x) hz
  apply toL2_injective
  apply Lp.ext
  exact (hQ.trans (Eventually.of_forall hpoint)).trans (hprod.trans
    (native_energyMulSmooth_toL2_ae g Ψ Ψ.smooth W).symm)

#print axioms nativeChartScaledCutoffTest_support
#print axioms nativeCoreCutoff_completed_identity
end Yamabe3.Analysis.SpherePolar
