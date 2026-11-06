import Yamabe3.Analysis.NativeCompactC2ChartEquation
import Yamabe3.Analysis.NativeWeakChartTransport
import Yamabe3.Analysis.NativeJacobianTestEquation
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Inclusion

/-! Actual native H1/L2-source pair of a compact closed H2 collar jet.
Both maps are constructed; their equation follows from the actual C2
chart equation and density, then holds for every completed native test. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic GreenParametrix
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private def compactClosedNativeH1Normed (g:RiemannianMetric 3 M) (O:Set M):
    NormedSpace ℝ (H1Zero g.leviCivitaData O):=inferInstance
attribute [local instance] compactClosedNativeH1Normed

def nativeCompactClosedJetFieldCLM
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (hOK:nativePoissonEntranceCollar⊆K)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆nativePoissonEntranceCollar) :
    nativeCollarJetClosure →L[ℝ] H1Zero g.leviCivitaData univ :=
  (inclusion (D:=g.leviCivitaData) (subset_univ (e '' nativePoissonEntranceCollar))).comp
    ((nativeWeakChartH1CLM g e he hei hK hKs hOK).comp (nativeCompactCollarEnergyCLM χ hχ hc hs))

theorem nativeCompactClosedJetField_C2_ae
    (g:RiemannianMetric 3 M) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) (hOK:nativePoissonEntranceCollar⊆K)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆nativePoissonEntranceCollar) (u:nativeC2OffZero) :
    (toL2 g.leviCivitaData univ
      (nativeCompactClosedJetFieldCLM g e he hei hK hKs hOK χ hχ hc hs (nativeC2CollarJetInclusion u)):M→ℝ)
      =ᵐ[g.volumeMeasure]nativeCompactChartFunction e K (nativeC2Cutoff χ hχ u).val := by
  simp only [nativeCompactClosedJetFieldCLM,ContinuousLinearMap.comp_apply,toL2_inclusion,
    toL2_nativeWeakChartH1CLM,nativeCompactCollarEnergyCLM_C2]
  have hh:=nativeCompactChart_congr_volume_ae g e he hei hK.measurableSet
    (ae_restrict_of_ae (s:=K) (nativeC2CutoffEnergyElement_ae χ hχ hc hs u))
  exact (nativeCompactChartL2Linear_ae g e he hei hK hKs _).trans hh

variable [CompactSpace M] [ConnectedSpace M]

theorem nativeCompactClosedJetSourcePair_test
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K U:Set E} (hK:IsCompact K) (hKU:K⊆U) (hU:IsOpen U) (hUs:U⊆e.source)
    (hOK:nativePoissonEntranceCollar⊆K)
    (hcoeff:∀x∈U,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆nativePoissonEntranceCollar)
    {r:ℝ} (hr:0<r) (hrs:closedBall (0:E) r⊆e.source)
    (β:ContDiffBump (0:E)) (hβ:β.rOut<r) (hχβ:tsupport χ⊆tsupport β)
    (J:nativeCollarJetClosure) (φ:EnergyTest g.leviCivitaData univ) :
    closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
      (nativeCompactClosedJetFieldCLM g e he hei hK (hKU.trans hUs) hOK χ hχ hc hs J)
      (φ:H1Zero g.leviCivitaData univ)=
      inner ℝ (nativeDensityChartSourceCLM g gE e he hei hK (hKU.trans hUs)
        (nativeCompactConformalSourceCLM gE χ hχ J))
        (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ)) := by
  have hclosed:IsClosed {J:nativeCollarJetClosure |
    closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
      (nativeCompactClosedJetFieldCLM g e he hei hK (hKU.trans hUs) hOK χ hχ hc hs J)
      (φ:H1Zero g.leviCivitaData univ)=
      inner ℝ (nativeDensityChartSourceCLM g gE e he hei hK (hKU.trans hUs)
        (nativeCompactConformalSourceCLM gE χ hχ J))
        (toL2 g.leviCivitaData univ (φ:H1Zero g.leviCivitaData univ))}:=
    isClosed_eq (by fun_prop) (by fun_prop)
  refine nativeC2CollarJetInclusion_dense.induction_on J hclosed ?_
  intro u
  rw [closedYamabeJacobianForm_test_eq_integral]
  simp only [zero_pow (by decide:(4:ℕ)≠0),mul_zero,zero_mul,sub_zero]
  calc
    _ = ∫y,(-8*g.leviCivitaData.laplacian φ y+g.leviCivitaData.scalarCurvature y*φ y)*
        nativeCompactChartFunction e K (nativeC2Cutoff χ hχ u).val y ∂g.volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [nativeCompactClosedJetField_C2_ae g e he hei hK (hKU.trans hUs) hOK χ hχ hc hs u] with y hy
      rw [hy]
    _ = ∫x in K,gE.pullbackVolumeDensity id x*
        (-8*gE.leviCivitaData.laplacian (nativeC2Cutoff χ hχ u).val x+
          gE.leviCivitaData.scalarCurvature x*(nativeC2Cutoff χ hχ u).val x)*φ (e x) :=
      nativeCompactC2_chart_conformal_equation g gE e he hei hK hKU hU hUs hcoeff
        χ hχ hc hs (hs.trans hOK) hr hrs β hβ hχβ u φ
    _ = ∫x in K,(nativeCompactConformalSourceCLM gE χ hχ (nativeC2CollarJetInclusion u):E→ℝ) x*φ (e x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (s:=K) (nativeCompactConformalSource_C2_ae gE hχ hs u)] with x hx
      rw [hx]
    _ = _ := (nativeDensityChartSourceCLM_pairing g gE e he hei hK (hKU.trans hUs)
      (fun x hx=>hcoeff x (hKU hx)) _ φ).symm

theorem nativeCompactClosedJetSourcePair_all_tests
    (g:RiemannianMetric 3 M) (gE:RiemannianMetric 3 E) (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K U:Set E} (hK:IsCompact K) (hKU:K⊆U) (hU:IsOpen U) (hUs:U⊆e.source)
    (hOK:nativePoissonEntranceCollar⊆K)
    (hcoeff:∀x∈U,gE.euclideanCoefficients x=g.pullbackCoefficients e x)
    (χ:E→ℝ) (hχ:ContDiff ℝ ∞ χ) (hc:HasCompactSupport χ)
    (hs:tsupport χ⊆nativePoissonEntranceCollar)
    {r:ℝ} (hr:0<r) (hrs:closedBall (0:E) r⊆e.source)
    (β:ContDiffBump (0:E)) (hβ:β.rOut<r) (hχβ:tsupport χ⊆tsupport β)
    (J:nativeCollarJetClosure) (η:H1Zero g.leviCivitaData univ) :
    closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const
      (nativeCompactClosedJetFieldCLM g e he hei hK (hKU.trans hUs) hOK χ hχ hc hs J) η=
      inner ℝ (nativeDensityChartSourceCLM g gE e he hei hK (hKU.trans hUs)
        (nativeCompactConformalSourceCLM gE χ hχ J)) (toL2 g.leviCivitaData univ η) := by
  induction η using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih φ =>
    exact nativeCompactClosedJetSourcePair_test g gE e he hei hK hKU hU hUs hOK hcoeff
      χ hχ hc hs hr hrs β hβ hχβ J φ

#print axioms nativeCompactClosedJetField_C2_ae
#print axioms nativeCompactClosedJetSourcePair_test
#print axioms nativeCompactClosedJetSourcePair_all_tests
end Yamabe3.Analysis.SpherePolar
