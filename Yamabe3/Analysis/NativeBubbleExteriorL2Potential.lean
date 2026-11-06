import Yamabe3.Analysis.NativeBubbleDelaunayCoupling
import Yamabe3.Analysis.NativePoissonExteriorCollarEquation
import Yamabe3.Analysis.NativeL2PotentialBinding

/-! Both true weighted convolution bounds for the literal bubble.
Reflection identifies the exterior coefficient with the opposite phase,
so the already constructed L2 particular inverse applies to that exact
coefficient. No new potential assumption is supplied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.Delaunay

theorem fullBubblePhasePotential_reflection (τ t : ℝ) :
    fullBubblePhasePotential (-τ) (-t)=fullBubblePhasePotential τ t := by
  change (15/4:ℝ)*fullBubbleDensity (-t+-τ)=(15/4)*fullBubbleDensity (t+τ)
  rw [show -t+-τ= -(t+τ) by ring,fullBubbleDensity_even]

theorem fullBubblePhasePotential_plus_kernel (τ t : ℝ) :
    (∫s : ℝ,spectralMajorant (5/2) 2 s*|fullBubblePhasePotential τ (t-s)|)≤
      (fullBubbleHighPotential τ).κ := by
  have he : (∫s : ℝ,spectralMajorant (5/2) 2 s*|fullBubblePhasePotential τ (t-s)|)=
      ∫s : ℝ,spectralMajorant (5/2) (-2) s*|fullBubblePhasePotential (-τ) (-t-s)| := by
    rw [←integral_neg_eq_self (fun s : ℝ => spectralMajorant (5/2) (-2) s*|fullBubblePhasePotential (-τ) (-t-s)|)]
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      have hk : spectralMajorant (5/2) (-2) (-s)=spectralMajorant (5/2) 2 s := by
        unfold spectralMajorant
        rw [abs_neg]
        congr 2
        ring
      dsimp only
      rw [hk,show -t-(-s)= -(t-s) by ring,fullBubblePhasePotential_reflection]
  rw [he]
  exact fullBubblePhasePotential_kernel (-τ) (-t)

theorem nativeBubbleExteriorPotential_eq_phase (t₀ : ℝ) :
    nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))=fullBubblePhasePotential t₀ := by
  ext t
  exact fullBubblePhasePotential_reflection t₀ t

#print axioms fullBubblePhasePotential_plus_kernel
#print axioms nativeBubbleExteriorPotential_eq_phase
end Yamabe3.Analysis.SpherePolar
