import Yamabe3.Analysis.NativePoissonExteriorInfiniteH2Collar
import Yamabe3.Analysis.NativePoissonReflectedCurve

/-! The exterior uses the actual Poisson curve at reversed time. The
joint representative is constructed and has the same modal coefficients. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

def nativePoissonExteriorCurve (P : NativeHighPotential) (b : AngularH1) (t : ℝ) : AngularL2 :=
  nativePoissonReflectedCurve P b (-t)

theorem nativePoissonExteriorCurve_continuous (P : NativeHighPotential) (b : AngularH1) :
    Continuous (nativePoissonExteriorCurve P b) :=
  (nativePoissonReflectedCurve_continuous P b).comp continuous_id.neg

theorem nativePoissonExteriorCurve_coefficient (P : NativeHighPotential) (b : AngularH1)
    (i : AngularIndex) (t : ℝ) :
    inner ℝ (angularBasis i) (nativePoissonExteriorCurve P b t) = nativePoissonExteriorExtension P b i t :=
  nativePoissonReflectedCurve_coefficient P b i (-t)

theorem nativePoissonExteriorCurve_finite_lift (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    cylinderLift (projectedAngular s (nativePoissonExteriorCurve P b)) = nativePoissonExteriorFiniteCollar P b s := by
  unfold projectedAngular
  simp_rw [nativePoissonExteriorCurve_coefficient]
  exact (finitePhysical_eq_lift s _).symm

theorem nativePoissonExteriorCurve_joint_representative (P : NativeHighPotential) (b : AngularH1) :
    ∃ w : ℝ × S → ℝ,StronglyMeasurable w ∧
      (∀ t,(fun θ => w (t,θ)) =ᵐ[angularVolume] (nativePoissonExteriorCurve P b t : S → ℝ)) ∧
      (∀ t,t ≤ 0 → (fun θ => w (t,θ)) =ᵐ[angularVolume] (P.curve b (-t) : S → ℝ)) := by
  obtain ⟨w,hw,hae⟩ := exists_joint_L2_representative_of_continuous (nativePoissonExteriorCurve_continuous P b)
  have hae' (t : ℝ) : (fun θ => w (t,θ)) =ᵐ[angularVolume] (nativePoissonExteriorCurve P b t : S → ℝ) := by
    simpa only [Measure.restrict_univ] using hae t
  refine ⟨w,hw,hae',fun t ht => ?_⟩
  simpa only [nativePoissonExteriorCurve,nativePoissonReflectedCurve,if_pos (neg_nonneg.mpr ht)] using hae' t

#print axioms nativePoissonExteriorCurve_coefficient
#print axioms nativePoissonExteriorCurve_joint_representative
end Yamabe3.Analysis.SpherePolar
