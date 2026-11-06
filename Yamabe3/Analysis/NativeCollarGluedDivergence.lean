import Yamabe3.Analysis.WeakSpherePiecewiseOperator
import Yamabe3.Analysis.NativeMatchedCollarRegularity
import Yamabe3.Analysis.NativeRescaledMetric

/-! The literal field glued from the already matched traces has the
actual rescaled native divergence source on each side. The proof uses
its proved H2 across the sphere, so no extra Gauss-coordinate premise
is imposed on the retained metric. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Elliptic

theorem nativeCollarGluedFunction_rescaled_divergence
    (g : RiemannianMetric 3 E) (r : ℝ) (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K)
    (hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K)
    {W : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWD : closure W⊆nativePoissonEntranceCollar) :
    MemWkp 2 2 (nativeCollarGluedFunction J.val.1 K.val.1) W ∧
      weakDivergenceSource W (nativeDivergenceMatrix (nativeRescaledMetric g r))
        (nativeCollarGluedFunction J.val.1 K.val.1) =ᵐ[volume.restrict W]
        physicalSplitSource (ball (0:E) 1)
          (weakDivergenceSource nativePoissonEntranceCollar (nativeScaledDivergenceMatrix g r) J.val.1)
          (weakDivergenceSource nativePoissonEntranceCollar (nativeScaledDivergenceMatrix g r) K.val.1) := by
  have hu := memWkp_on_precompact_of_locally
    (nativeCollarGluedFunction_local_H2 J K hv hn) hW hWc hWD
  refine ⟨hu,?_⟩
  rw [nativeRescaledMetric_divergenceMatrix]
  exact weakDivergenceSource_sphere_piecewise_ae hW (subset_closure.trans hWD)
    (nativeScaledDivergenceMatrix g r) hu (nativeCollarJetClosure_memH2 J)
    (nativeCollarJetClosure_memH2 K) (Filter.EventuallyEq.refl _ _)

#print axioms nativeCollarGluedFunction_rescaled_divergence
end Yamabe3.Analysis.SpherePolar
