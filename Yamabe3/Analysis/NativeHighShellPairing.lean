import Yamabe3.Analysis.NativeShellLiftPairing
import Yamabe3.Analysis.NativeAngularProjectionPairing

/-! The actual high-source return pairing, retaining the projection and
its loss of low modes. Time translation is the same source translation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeHighPhysicalSource_weighted_pairing
    (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    (∫ x in nativePoissonEntranceCollar,nativeShellSourceWeight x*
      (nativeL2HighPhysicalSourceCLM F : E → ℝ) x*(nativeL2HighPhysicalSourceCLM G : E → ℝ) x)=
      ∫ t in Ioc (-(1/4:ℝ)) (1/4),inner ℝ
        (nativeHighProjection (angularBasis.repr.symm (F t)))
        (nativeHighProjection (angularBasis.repr.symm (G t))) := by
  have h := nativeShell_weighted_lift_pairing (nativeL2HighAngularCLM F) (nativeL2HighAngularCLM G)
  apply h.trans
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := Ioc (-(1/4:ℝ)) (1/4)) (nativeL2HighAngularCLM_ae F),
    ae_restrict_of_ae (s := Ioc (-(1/4:ℝ)) (1/4)) (nativeL2HighAngularCLM_ae G)] with t hf hg
  rw [hf,hg]

theorem nativeShellSourceReturn_high_source_pairing (s : ℝ)
    (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    inner ℝ (nativeShellSourceReturnCLM s
      (nativeL2HighPhysicalSourceCLM (l2TimeTranslateCLM (SpectralSpace AngularIndex) s F))) G=
      ∫ t in Ioc (-(1/4:ℝ)) (1/4),inner ℝ
        (nativeHighProjection (angularBasis.repr.symm (F (t+s))))
        (nativeHighProjection (angularBasis.repr.symm (G (t+s)))) := by
  rw [nativeShellSourceReturn_pairing,nativeHighPhysicalSource_weighted_pairing]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (s := Ioc (-(1/4:ℝ)) (1/4))
    (l2TimeTranslate_ae (SpectralSpace AngularIndex) s F),
    ae_restrict_of_ae (s := Ioc (-(1/4:ℝ)) (1/4))
    (l2TimeTranslate_ae (SpectralSpace AngularIndex) s G)] with t hf hg
  rw [hf,hg]

#print axioms nativeHighPhysicalSource_weighted_pairing
#print axioms nativeShellSourceReturn_high_source_pairing
end Yamabe3.Analysis.SpherePolar
