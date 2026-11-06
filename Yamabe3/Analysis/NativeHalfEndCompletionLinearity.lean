import Yamabe3.Analysis.NativeHalfEndCompletionChoice
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Resolvent

/-! Linearity of the one canonical completion follows from the actual
linear physical L2 solver and the proved toL2 injection. It is not inferred
from an arbitrary choice of pointwise representatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}
variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (P : ℝ →ᵇ ℝ)
  (hP : ∀ t, (∫ s : ℝ, spectralMajorant (5/2) (-2) s*|P (t-s)|) ≤ κ)
  (hP0 : ∀ t, 0 ≤ P t) (hPs : ContDiff ℝ ∞ (fun t : ℝ => P t))

theorem nativeHalfEndCompletion_rep_physicalL2 (f : HalfEndHighH2Source) :
    (toL2 nativeWeakEuclideanD O (nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs f) : E → ℝ)
      =ᵐ[volume] (O).indicator (nativeHalfEndH2SourcePhysicalL2CLM hκ0 hκ1 P hP hP0 f : E → ℝ) := by
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  have hp := (nativeHalfEndH2Source_same_solution hκ0 hκ1 P hP hP0 hPs f).2.1
  have hp' := (ae_restrict_iff' hO.measurableSet).mp hp
  filter_upwards [nativeHalfEndH2SourceCompletion_rep hκ0 hκ1 P hP hP0 hPs f,hp'] with x hz hx
  rw [hz]
  by_cases hxO : x ∈ O
  · simp only [indicator_of_mem hxO,hx hxO]
  · simp only [indicator_of_notMem hxO]

theorem nativeHalfEndH2SourceCompletion_add (f g : HalfEndHighH2Source) :
    nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs (f+g) =
      nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs f +
      nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs g := by
  apply toL2_injective (D := nativeWeakEuclideanD) (Ω := O)
  rw [map_add]
  apply Lp.ext
  simp only [native_euclideanMetric_volumeMeasure]
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  let C := nativeHalfEndH2SourcePhysicalL2CLM hκ0 hκ1 P hP hP0
  have hc : (C (f+g) : E → ℝ) =ᵐ[volume.restrict O] fun x => (C f : E → ℝ) x+(C g : E → ℝ) x := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hc' := (ae_restrict_iff' hO.measurableSet).mp hc
  have hz := Lp.coeFn_add
    (toL2 nativeWeakEuclideanD O (nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs f))
    (toL2 nativeWeakEuclideanD O (nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs g))
  simp only [native_euclideanMetric_volumeMeasure] at hz
  filter_upwards [nativeHalfEndCompletion_rep_physicalL2 hκ0 hκ1 P hP hP0 hPs (f+g),
    nativeHalfEndCompletion_rep_physicalL2 hκ0 hκ1 P hP hP0 hPs f,
    nativeHalfEndCompletion_rep_physicalL2 hκ0 hκ1 P hP hP0 hPs g,hz,hc'] with x hfg hf hg hz hc
  rw [hz,hfg,Pi.add_apply,hf,hg]
  by_cases hx : x ∈ O
  · simp only [indicator_of_mem hx]
    exact hc hx
  · simp only [indicator_of_notMem hx,zero_add]

theorem nativeHalfEndH2SourceCompletion_smul (c : ℝ) (f : HalfEndHighH2Source) :
    nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs (c • f) =
      c • nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs f := by
  apply toL2_injective (D := nativeWeakEuclideanD) (Ω := O)
  rw [map_smul]
  apply Lp.ext
  simp only [native_euclideanMetric_volumeMeasure]
  have hO : IsOpen O := Metric.isOpen_ball.sdiff isClosed_singleton
  let C := nativeHalfEndH2SourcePhysicalL2CLM hκ0 hκ1 P hP hP0
  have hc : (C (c • f) : E → ℝ) =ᵐ[volume.restrict O] fun x => c*(C f : E → ℝ) x := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hc' := (ae_restrict_iff' hO.measurableSet).mp hc
  have hz := Lp.coeFn_smul c
    (toL2 nativeWeakEuclideanD O (nativeHalfEndH2SourceCompletion hκ0 hκ1 P hP hP0 hPs f))
  simp only [native_euclideanMetric_volumeMeasure] at hz
  filter_upwards [nativeHalfEndCompletion_rep_physicalL2 hκ0 hκ1 P hP hP0 hPs (c • f),
    nativeHalfEndCompletion_rep_physicalL2 hκ0 hκ1 P hP hP0 hPs f,hz,hc'] with x hcf hf hz hc
  change _ = c * _ at hz
  rw [hz,hcf,hf]
  by_cases hx : x ∈ O
  · simp only [indicator_of_mem hx]
    exact hc hx
  · simp only [indicator_of_notMem hx,mul_zero]

#print axioms nativeHalfEndCompletion_rep_physicalL2
#print axioms nativeHalfEndH2SourceCompletion_add
#print axioms nativeHalfEndH2SourceCompletion_smul
end Yamabe3.Analysis.UniformElliptic
