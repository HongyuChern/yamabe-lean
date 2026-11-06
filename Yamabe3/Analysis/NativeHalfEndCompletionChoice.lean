import Yamabe3.Analysis.NativeHalfEndRetainedEquation

/-! Fix one completion element per source before considering any chart.
Choice selects a proved realization; the weak equation and norm bound are
outputs of the same construction, not structure inputs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction InnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open PoincareMT.LeviCivitaData.Dirichlet
local notation "D" => nativeWeakEuclideanD
local notation "O" => Metric.ball (0 : E) 1 \ {(0 : E)}
variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t) (hVs : ContDiff ℝ ∞ (fun t : ℝ => V t))

def nativeHalfEndH2SourceCompletion (f : HalfEndHighH2Source) : H1Zero D O :=
  (nativeHalfEndH2Source_retained_equation hκ0 hκ1 V hV hV0 hVs f).choose

def nativeHalfEndH2SourceCompletionRHS (f : HalfEndHighH2Source) :
    Lp ℝ 2 (RiemannianMetric.euclideanMetric 3).volumeMeasure :=
  (nativeHalfEndH2Source_retained_equation hκ0 hκ1 V hV hV0 hVs f).choose_spec.choose

theorem nativeHalfEndH2SourceCompletion_rep (f : HalfEndHighH2Source) :
    (toL2 D O (nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f) : E → ℝ) =ᵐ[volume]
      (O).indicator (cylinderLift (nativeHalfEndH2SourceJoint hκ0 hκ1 V hV hV0 f)) :=
  (nativeHalfEndH2Source_retained_equation hκ0 hκ1 V hV hV0 hVs f).choose_spec.choose_spec.1

theorem nativeHalfEndH2SourceCompletion_source (f : HalfEndHighH2Source) :
    (nativeHalfEndH2SourceCompletionRHS hκ0 hκ1 V hV hV0 hVs f : E → ℝ)
      =ᵐ[(RiemannianMetric.euclideanMetric 3).volumeMeasure]
      (O).indicator (fun x => halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f.1) x / 8 +
        nativeHalfEndPotentialCoefficient V x *
          toL2 D O (nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f) x) :=
  (nativeHalfEndH2Source_retained_equation hκ0 hκ1 V hV hV0 hVs f).choose_spec.choose_spec.2.1

theorem nativeHalfEndH2SourceCompletion_weak_equation (f : HalfEndHighH2Source)
    (v : H1Zero D O) :
    ⟪nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f, v⟫_ℝ -
      ⟪toL2 D O (nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f), toL2 D O v⟫_ℝ =
      ⟪nativeHalfEndH2SourceCompletionRHS hκ0 hκ1 V hV hV0 hVs f, toL2 D O v⟫_ℝ :=
  (nativeHalfEndH2Source_retained_equation hκ0 hκ1 V hV hV0 hVs f).choose_spec.choose_spec.2.2.1 v

theorem nativeHalfEndH2SourceCompletion_norm_sq (f : HalfEndHighH2Source) :
    ‖nativeHalfEndH2SourceCompletion hκ0 hκ1 V hV hV0 hVs f‖^2 ≤
      ((2 / (((5 / 2 : ℝ)^2 - 4) * (1-κ)^2))^2 / 6 +
        (nativeHalfHighDirichletEnergyBound κ V ^ 2 + nativeHalfHighDirichletDerivativeBound κ V ^ 2) / 2) *
        ‖halfEndH2SourceToAngularCLM f.1‖^2 :=
  (nativeHalfEndH2Source_retained_equation hκ0 hκ1 V hV hV0 hVs f).choose_spec.choose_spec.2.2.2

#print axioms nativeHalfEndH2SourceCompletion_rep
#print axioms nativeHalfEndH2SourceCompletion_source
#print axioms nativeHalfEndH2SourceCompletion_weak_equation
#print axioms nativeHalfEndH2SourceCompletion_norm_sq
end Yamabe3.Analysis.UniformElliptic
