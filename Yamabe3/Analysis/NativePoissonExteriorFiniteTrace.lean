import Yamabe3.Analysis.NativePoissonExteriorCollarIdentification
import Yamabe3.Analysis.NativeL2HalfNormalTrace

/-! Actual exterior entrance traces: reversing cylinder time changes
only the first derivative. The physical conformal half-weight remains. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
theorem nativePoissonExteriorFiniteCollar_entrance (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) (θ : S) :
    nativePoissonExteriorFiniteCollar P b s (θ:E) =
      finiteAngular s (fun i _ => nativePoissonCoordinate P b i 0) (0,θ) ∧
    fderiv ℝ (nativePoissonExteriorFiniteCollar P b s) (θ:E) (θ:E) =
      -finiteAngular s (fun i _ => -inner ℝ (angularBasis i) (P.curveDerivative b 0)+
        nativePoissonCoordinate P b i 0/2) (0,θ) := by
  let q := nativePoissonExteriorExtension P b
  have hq (i : AngularIndex) : ContDiff ℝ 2 (q i) := P.exteriorExtension_C2 b i
  have hj (i : AngularIndex) := P.exteriorExtension_jets b i 0 le_rfl
  simp only [neg_zero] at hj
  have hx : (θ:E) ≠ 0 := by
    have h := norm_eq_of_mem_sphere θ
    intro he
    rw [he,norm_zero] at h
    norm_num at h
  have hu := (finitePhysical_contDiffOn_offZero_C2 s q (fun i _ => hq i)).contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hr := native_finitePhysical_radial_derivative s q (by norm_num : (0:ℝ)<1) θ
    (fun i _ => (hq i).differentiable (by norm_num) _)
    (by simpa only [one_smul] using hu.differentiableAt (by norm_num))
  have hscale : radialScale 1 = 1 := by simp [radialScale]
  simp only [one_smul,Real.log_one,neg_zero,hscale,div_one,neg_one_mul] at hr
  constructor
  · change finitePhysical s q (θ:E) = _
    rw [finitePhysical_eq_lift,show (θ:E)=(1:ℝ) • (θ:E) from (one_smul _ _).symm,
      cylinderLift_smul _ (by norm_num) θ,Real.log_one,neg_zero,hscale,one_mul]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [q]
    rw [(hj i).1]
  · change fderiv ℝ (finitePhysical s q) (θ:E) (θ:E) = _
    rw [hr]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [q]
    rw [(hj i).1,(hj i).2.1]

def nativePoissonExteriorPhysicalEntranceNormal (P : NativeHighPotential) (b : AngularH1) : AngularL2 :=
  -P.dtn b-(1/2:ℝ) • P.curve b 0

theorem nativePoissonExteriorFiniteCollar_value_trace_ae (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    (fun θ : S => nativePoissonExteriorFiniteCollar P b s (θ:E)) =ᵐ[angularVolume]
      (⇑(finiteHilbertProjection angularBasis s (P.curve b 0))) := by
  have he : (fun θ : S => nativePoissonExteriorFiniteCollar P b s (θ:E)) =
      (fun θ => projectedAngular s (P.curve b) (0,θ)) := by
    funext θ
    simpa only [projectedAngular,finiteAngular,nativePoissonCoordinate] using (nativePoissonExteriorFiniteCollar_entrance P b s θ).1
  rw [he]
  exact projectedAngular_ae s (P.curve b) 0


theorem nativePoissonExteriorFiniteCollar_normal_trace_ae (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    (fun θ : S => fderiv ℝ (nativePoissonExteriorFiniteCollar P b s) (θ:E) (θ:E)) =ᵐ[angularVolume]
      (⇑(finiteHilbertProjection angularBasis s (nativePoissonExteriorPhysicalEntranceNormal P b))) := by
  have hD : P.dtn b = -P.curveDerivative b 0 := rfl
  have he : (fun θ : S => fderiv ℝ (nativePoissonExteriorFiniteCollar P b s) (θ:E) (θ:E)) =
      (fun θ => projectedAngular s (fun _ => nativePoissonExteriorPhysicalEntranceNormal P b) (0,θ)) := by
    funext θ
    rw [(nativePoissonExteriorFiniteCollar_entrance P b s θ).2]
    unfold projectedAngular finiteAngular nativePoissonExteriorPhysicalEntranceNormal
    rw [hD,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [nativePoissonCoordinate,inner_sub_right,inner_neg_right,neg_neg,real_inner_smul_right]
    ring
  rw [he]
  exact projectedAngular_ae s (fun _ => nativePoissonExteriorPhysicalEntranceNormal P b) 0


#print axioms nativePoissonExteriorFiniteCollar_entrance
#print axioms nativePoissonExteriorFiniteCollar_value_trace_ae
#print axioms nativePoissonExteriorFiniteCollar_normal_trace_ae
end Yamabe3.Analysis.SpherePolar
