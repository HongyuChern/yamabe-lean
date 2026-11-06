import Yamabe3.Analysis.NativeCollarInteriorSourceIdentity
import Yamabe3.Analysis.NativeCollarExteriorSourceIdentity

/-! The retained inner and outer equations give the actual piecewise
source of the one glued field. Sphere-nullness is used only for volume
identities; the trace matching used to obtain H2 is kept separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped ContDiff ENNReal Topology BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Delaunay
open Poincare.Analysis.Sobolev.Euclidean

lemma physicalSplitSource_collar_congr {W : Set E} (hW : IsOpen W)
    (hWD : W⊆nativePoissonEntranceCollar) {f g f' g' : E → ℝ}
    (hi : f=ᵐ[volume.restrict nativePositiveEntranceCollar] f')
    (ho : g=ᵐ[volume.restrict nativeNegativeEntranceCollar] g') :
    physicalSplitSource (ball (0:E) 1) f g=ᵐ[volume.restrict W]
      physicalSplitSource (ball (0:E) 1) f' g' := by
  classical
  have hI : IsOpen nativePositiveEntranceCollar := (nativePolarTimeWindow_open (1/2)).inter isOpen_ball
  have hO : IsOpen nativeNegativeEntranceCollar :=
    (nativePolarTimeWindow_open (1/2)).inter (isOpen_lt continuous_const continuous_norm)
  have hn : ∀ᵐ x : E ∂volume,x∉sphere (0:E) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0:E) 1)
  filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' hI.measurableSet).mp hi),
    ae_restrict_of_ae ((ae_restrict_iff' hO.measurableSet).mp ho),
    ae_restrict_of_ae hn,ae_restrict_mem hW.measurableSet] with x hxI hxO hxn hxW
  by_cases hx : x∈ball (0:E) 1
  · simpa only [physicalSplitSource,piecewise_eq_of_mem _ _ _ hx] using hxI ⟨hWD hxW,hx⟩
  · have hne : ‖x‖≠1 := by simpa only [mem_sphere,dist_zero_right] using hxn
    have hle : 1≤‖x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hx
    have hgt : 1<‖x‖ := lt_of_le_of_ne hle hne.symm
    simpa only [physicalSplitSource,piecewise_eq_of_notMem _ _ _ hx] using hxO ⟨hWD hxW,hgt⟩

theorem nativeCollarGluedFunction_original_sources
    (g : RiemannianMetric 3 E) (r : ℝ) (v : ℝ → ℝ) (phase : ℝ)
    (V : ℝ →ᵇ ℝ) (J K : nativeCollarJetClosure)
    (hv : nativeCollarValueTraceCLM J=nativeCollarValueTraceCLM K)
    (hn : nativeCollarNormalTraceCLM J=nativeCollarNormalTraceCLM K)
    {u f q : E → ℝ}
    (hJu : (J.val.1 : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar] u)
    (hi : ∀ W : Set E,IsOpen W → IsCompact (closure W) → closure W⊆(ball (0:E) 1\{(0:E)}) →
      nativeWeakRescaledDelaunayJacobian W g r v phase u=ᵐ[volume.restrict W] f)
    (ho : (nativeExteriorNativeJacobianCLM g r V K.val : E → ℝ)=ᵐ[volume.restrict nativeNegativeEntranceCollar] q)
    {W : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWD : closure W⊆nativePoissonEntranceCollar) :
    MemWkp 2 2 (nativeCollarGluedFunction J.val.1 K.val.1) W ∧
      weakDivergenceSource W (nativeDivergenceMatrix (nativeRescaledMetric g r))
        (nativeCollarGluedFunction J.val.1 K.val.1)=ᵐ[volume.restrict W]
          physicalSplitSource (ball (0:E) 1)
            (fun x => f x-(annularDelaunayPotential v phase x+nativeDelaunayPotentialError g r v phase x)*(J.val.1 : E → ℝ) x)
            (fun x => q x/8-nativeExteriorDivergencePotential g r V x*(K.val.1 : E → ℝ) x) := by
  have hh := nativeCollarGluedFunction_rescaled_divergence g r J K hv hn hW hWc hWD
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact physicalSplitSource_collar_congr hW (subset_closure.trans hWD)
    (nativeCollarJet_original_inner_source g r v phase J hJu hi)
    (nativeCollarJet_original_outer_source g r V K ho)

#print axioms physicalSplitSource_collar_congr
#print axioms nativeCollarGluedFunction_original_sources
end Yamabe3.Analysis.SpherePolar
