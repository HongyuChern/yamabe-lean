import Yamabe3.Analysis.NativeCollarGluedDivergence
import Yamabe3.Analysis.AEPrecompactLocality
import Yamabe3.Analysis.NativePoissonPositiveCollarEquation

/-! The original local native equation identifies the same retained
entrance jet's positive-side divergence source. The open-side cover does
not demand a precompact set whose closure avoids the entrance sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Delaunay
open Poincare.Analysis.Sobolev.Euclidean
local notation "O" => (ball (0:E) 1 \ {(0:E)})

theorem nativeCollarJet_original_inner_source
    (g : RiemannianMetric 3 E) (r : ℝ) (v : ℝ → ℝ) (phase : ℝ)
    (J : nativeCollarJetClosure) {u f : E → ℝ}
    (hJu : (J.val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u)
    (heq : ∀ W : Set E,IsOpen W → IsCompact (closure W) → closure W⊆O →
      nativeWeakRescaledDelaunayJacobian W g r v phase u=ᵐ[volume.restrict W] f) :
    weakDivergenceSource nativePoissonEntranceCollar (nativeScaledDivergenceMatrix g r) J.val.1
      =ᵐ[volume.restrict nativePositiveEntranceCollar]
        fun x => f x-(annularDelaunayPotential v phase x+nativeDelaunayPotentialError g r v phase x)*(J.val.1 : E → ℝ) x := by
  apply ae_eq_restrict_of_precompact_local ((nativePolarTimeWindow_open (1/2)).inter isOpen_ball)
  intro W hW hWc hWI
  have hWD : W⊆nativePoissonEntranceCollar := fun x hx => (hWI (subset_closure hx)).1
  have hWO : closure W⊆O := by
    intro x hx
    have hi := hWI hx
    exact ⟨hi.2,by simpa only [mem_singleton_iff] using hi.1.1⟩
  have hJuW := ae_restrict_of_ae_restrict_of_subset hWD hJu
  have hJW := (nativeCollarJetClosure_memH2 J).mono_set (by norm_num : (1:ℝ≥0∞)≤2) hW hWD
  have huW := (MemWkp_congr_ae (by norm_num : (1:ℝ≥0∞)≤2) hW hJuW).mp hJW
  have hop := weakDivergenceSource_same_on_overlap hW hWD (subset_refl W)
    (nativeScaledDivergenceMatrix g r) (nativeCollarJetClosure_memH2 J) huW hJuW
  have hs := heq W hW hWc hWO
  rw [nativeWeakJacobian_eq_divergence] at hs
  filter_upwards [hop,hs,hJuW] with x hx hy hz
  change weakDivergenceSource nativePoissonEntranceCollar (nativeScaledDivergenceMatrix g r) J.val.1 x=_
  rw [hx,hz]
  exact eq_sub_of_add_eq hy

#print axioms nativeCollarJet_original_inner_source
end Yamabe3.Analysis.SpherePolar
