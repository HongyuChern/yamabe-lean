import Yamabe3.Analysis.NativeCompletedChartScaling
import Yamabe3.Analysis.NativeLocalCanonicalSphereTrace

/-! The physically signed corrected field is ONE native completion
element: L(TX) + chi_core*R(TX) - R(TX). Its literal native-volume L2
identity is proved. Source/PDE cancellation is a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
local notation "Deuc" => nativeWeakEuclideanD
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private def feedbackCorrectedH1Normed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] feedbackCorrectedH1Normed

def nativeChartScaledCutoffTest
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a:ℝ} (ha:0 < a) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (O:Set E) (hs:tsupport χ⊆O) (hfit:euclideanDilatedDomain a O⊆e.source) :
    EnergyTest g.leviCivitaData univ :=
  let φ:EnergyTest Deuc O:=⟨χ,hχ.contMDiff,hc,hs⟩
  let ψ:=nativeWeakChartTest g e hei hfit (euclideanDilatedTest ha O φ)
  ⟨ψ,ψ.smooth,ψ.hasCompactSupport,subset_univ _⟩

theorem nativeChartScaledCutoffTest_apply
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a:ℝ} (ha:0 < a) (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (O:Set E) (hs:tsupport χ⊆O) (hfit:euclideanDilatedDomain a O⊆e.source)
    (x:E) (hx:a • x∈e.source) :
    nativeChartScaledCutoffTest g e hei ha χ hχ hc O hs hfit (e (a • x))=χ x := by
  change coordinateExtension e (fun y:E=>χ (a⁻¹ • y)) (e (a • x))=χ x
  rw [coordinateExtension_comp_apply e _ hx,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]

variable [CompactSpace M] [ConnectedSpace M]
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (g:RiemannianMetric 3 M) (χ:M→ℝ) (hχ:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ χ)
  (L:X →L[ℝ] H1Zero g.leviCivitaData univ) (T:X →L[ℝ] X) (R:X →L[ℝ] H1Zero g.leviCivitaData univ)

def nativeNegativeFeedbackEnergyCLM : X →L[ℝ] H1Zero g.leviCivitaData univ :=
  L.comp T+(energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) χ hχ).comp (R.comp T)-R.comp T

theorem nativeNegativeFeedbackEnergyCLM_ae (x:X) :
    (toL2 g.leviCivitaData univ (nativeNegativeFeedbackEnergyCLM g χ hχ L T R x):M→ℝ)=ᵐ[g.volumeMeasure]
      fun y=>toL2 g.leviCivitaData univ (L (T x)) y-(1-χ y)*toL2 g.leviCivitaData univ (R (T x)) y := by
  let Mχ:=energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) χ hχ
  let z:=toL2 g.leviCivitaData univ (L (T x))
  let m:=toL2 g.leviCivitaData univ (Mχ (R (T x)))
  let r:=toL2 g.leviCivitaData univ (R (T x))
  have hh:toL2 g.leviCivitaData univ (nativeNegativeFeedbackEnergyCLM g χ hχ L T R x)=z+m-r := by
    simp only [nativeNegativeFeedbackEnergyCLM,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,map_sub,map_add,z,m,r,Mχ]
  rw [hh]
  filter_upwards [Lp.coeFn_sub (z+m) r,Lp.coeFn_add z m,
    native_energyMulSmooth_toL2_ae g χ hχ (R (T x))] with y hs ha hm
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ha]
  simp only [Pi.add_apply]
  change z y+m y-r y=_
  change m y=χ y*r y at hm
  rw [hm]
  change z y+χ y*r y-r y=z y-(1-χ y)*r y
  ring

#print axioms nativeChartScaledCutoffTest_apply
#print axioms nativeNegativeFeedbackEnergyCLM_ae
end Yamabe3.Analysis.SpherePolar
