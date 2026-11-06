import Yamabe3.Analysis.NativeHighShellPairing
import Yamabe3.Analysis.NativeLogShellIntegrals

/-! The actual shell source return reconstructs the positive-time high
source in weak pairing. This explicitly retains the high projection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeHighSourcePairing (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) (t : ℝ) : ℝ :=
  inner ℝ (nativeHighProjection (angularBasis.repr.symm (F t)))
    (nativeHighProjection (angularBasis.repr.symm (G t)))

theorem nativeHighSourcePairing_integrable
    (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    Integrable (nativeHighSourcePairing F G) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (nativeL2HighAngularCLM F) (nativeL2HighAngularCLM G)).congr
  filter_upwards [nativeL2HighAngularCLM_ae F,nativeL2HighAngularCLM_ae G] with t hf hg
  dsimp only [nativeHighSourcePairing]
  rw [hf,hg]

theorem nativeHighSourceReturn_reconstructs
    (F G : Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ)) :
    HasSum (fun n : ℕ => inner ℝ
      (nativeShellSourceReturnCLM (nativeLogShellCenter n)
        (nativeL2HighPhysicalSourceCLM
          (l2TimeTranslateCLM (SpectralSpace AngularIndex) (nativeLogShellCenter n) F))) G)
      (∫ t in Ioi 0,nativeHighSourcePairing F G t) := by
  have h := nativeLogShell_integrals_hasSum (nativeHighSourcePairing F G)
    (nativeHighSourcePairing_integrable F G).integrableOn
  simpa only [nativeShellSourceReturn_high_source_pairing,nativeHighSourcePairing] using h

#print axioms nativeHighSourcePairing_integrable
#print axioms nativeHighSourceReturn_reconstructs
end Yamabe3.Analysis.SpherePolar
