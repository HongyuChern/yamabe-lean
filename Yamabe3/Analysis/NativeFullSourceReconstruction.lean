import Yamabe3.Analysis.NativeFullShellReturn
import Yamabe3.Analysis.NativeShellLiftPairing
import Yamabe3.Analysis.NativeLogShellIntegrals

/-! The actual full weighted source return reconstructs every positive
L2 test, with no high-mode restriction on the test or the source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeFullPhysicalSource_weighted_pairing
    (F G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    (∫ x in nativePoissonEntranceCollar,nativeShellSourceWeight x*
      (nativeL2FullPhysicalSourceCLM F : E → ℝ) x*(nativeL2FullPhysicalSourceCLM G : E → ℝ) x)=
      ∫ t in Ioc (-(1/4:ℝ)) (1/4),inner ℝ (F t) (G t) := by
  have h := nativeShell_weighted_lift_pairing (nativeL2FullAngularCLM F) (nativeL2FullAngularCLM G)
  apply h.trans
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := Ioc (-(1/4:ℝ)) (1/4)) (nativeL2FullAngularCLM_ae F),
    ae_restrict_of_ae (s := Ioc (-(1/4:ℝ)) (1/4)) (nativeL2FullAngularCLM_ae G)] with t hf hg
  rw [hf,hg]
  exact angularBasis.repr.symm.inner_map_map (F t) (G t)

theorem nativeFullShellSourceReturn_source_pairing (s : ℝ)
    (F G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    inner ℝ (nativeFullShellSourceReturnCLM s
      (nativeL2FullPhysicalSourceCLM (l2TimeTranslateCLM AngularSpectralSpace s F))) G=
      ∫ t in Ioc (-(1/4:ℝ)) (1/4),inner ℝ (F (t+s)) (G (t+s)) := by
  rw [nativeFullShellSourceReturn_pairing,nativeFullPhysicalSource_weighted_pairing]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := Ioc (-(1/4:ℝ)) (1/4))
    (l2TimeTranslate_ae AngularSpectralSpace s F),
    ae_restrict_of_ae (s := Ioc (-(1/4:ℝ)) (1/4))
    (l2TimeTranslate_ae AngularSpectralSpace s G)] with t hf hg
  rw [hf,hg]

theorem nativeFullSourceReturn_reconstructs
    (F G : Lp AngularSpectralSpace 2 (volume : Measure ℝ)) :
    HasSum (fun n : ℕ => inner ℝ
      (nativeFullShellSourceReturnCLM (nativeLogShellCenter n)
        (nativeL2FullPhysicalSourceCLM
          (l2TimeTranslateCLM AngularSpectralSpace (nativeLogShellCenter n) F))) G)
      (∫ t in Ioi 0,inner ℝ (F t) (G t)) := by
  have h := nativeLogShell_integrals_hasSum (fun t => inner ℝ (F t) (G t))
    (L2.integrable_inner (𝕜 := ℝ) F G).integrableOn
  simpa only [nativeFullShellSourceReturn_source_pairing] using h

theorem nativeFullPositiveTest_pairing
    (F G : Lp AngularSpectralSpace 2 (volume : Measure ℝ))
    (hG0 : ∀ᵐ t : ℝ ∂volume,t≤0 → G t=0) :
    inner ℝ F G=∫ t in Ioi 0,inner ℝ (F t) (G t) := by
  rw [L2.inner_def,←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [hG0] with t hzero
  by_cases ht : 0<t
  · rw [indicator_of_mem (show t∈Ioi (0:ℝ) from ht)]
  · rw [indicator_of_notMem (show t∉Ioi (0:ℝ) from ht),hzero (le_of_not_gt ht),inner_zero_right]

#print axioms nativeFullPhysicalSource_weighted_pairing
#print axioms nativeFullShellSourceReturn_source_pairing
#print axioms nativeFullSourceReturn_reconstructs
#print axioms nativeFullPositiveTest_pairing
end Yamabe3.Analysis.SpherePolar
