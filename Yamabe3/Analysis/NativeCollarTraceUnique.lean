import Yamabe3.Analysis.NativeCollarTraceDifference
import Yamabe3.Analysis.L2ApproximationIdentity

/-! Value and normal boundary limits are independent of a C2 approximation
with the same strong volume jets. All boundary equalities use native area. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

theorem native_C1_sphere_normal_memLp {u : E → ℝ}
    (hu : ContDiffOn ℝ 1 u ({0}ᶜ : Set E)) :
    MemLp (fun θ : S => fderiv ℝ u (θ:E) (θ:E)) 2 angularVolume := by
  apply native_continuous_sphere_memLp
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hO : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have hx : (θ:E) ≠ 0 := by
    intro h
    have hn := norm_eq_of_mem_sphere θ
    rw [h,norm_zero] at hn
    norm_num at hn
  exact ((hu.continuousOn_fderiv_of_isOpen hO (by norm_num)).continuousAt (hO.mem_nhds hx) |>.comp
    continuous_subtype_val.continuousAt).clm_apply continuous_subtype_val.continuousAt

theorem native_C2_collar_trace_limits_unique {ι : Type*} {l : Filter ι} [NeBot l]
    (u v : ι → E → ℝ)
    (hu : ∀ a,ContDiffOn ℝ 2 (u a) ({0}ᶜ : Set E))
    (hv : ∀ a,ContDiffOn ℝ 2 (v a) ({0}ᶜ : Set E))
    (hvalue : Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,(u a x-v a x)^2) l (𝓝 0))
    (hfirst : ∀ j,Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,
      (nativeCoordinateFirst j (u a) x-nativeCoordinateFirst j (v a) x)^2) l (𝓝 0))
    (hsecond : ∀ k j,Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,
      (nativeCoordinateSecond k j (u a) x-nativeCoordinateSecond k j (v a) x)^2) l (𝓝 0))
    {τu τv νu νv : S → ℝ}
    (hτu : MemLp τu 2 angularVolume) (hτv : MemLp τv 2 angularVolume)
    (hνu : MemLp νu 2 angularVolume) (hνv : MemLp νv 2 angularVolume)
    (htu : Tendsto (fun a => ∫ θ : S,(u a (θ:E)-τu θ)^2 ∂angularVolume) l (𝓝 0))
    (htv : Tendsto (fun a => ∫ θ : S,(v a (θ:E)-τv θ)^2 ∂angularVolume) l (𝓝 0))
    (hnu : Tendsto (fun a => ∫ θ : S,(fderiv ℝ (u a) (θ:E) (θ:E)-νu θ)^2 ∂angularVolume) l (𝓝 0))
    (hnv : Tendsto (fun a => ∫ θ : S,(fderiv ℝ (v a) (θ:E) (θ:E)-νv θ)^2 ∂angularVolume) l (𝓝 0)) :
    τu =ᵐ[angularVolume] τv ∧ νu =ᵐ[angularVolume] νv := by
  have h := native_C2_collar_trace_difference_zero u v hu hv hvalue hfirst hsecond
  exact ⟨native_ae_eq_of_approaching_L2_approximants
      (fun a => native_C1_sphere_restriction_memLp (hu a).continuousOn)
      (fun a => native_C1_sphere_restriction_memLp (hv a).continuousOn) hτu hτv htu htv h.1,
    native_ae_eq_of_approaching_L2_approximants
      (fun a => native_C1_sphere_normal_memLp ((hu a).of_le (by norm_num)))
      (fun a => native_C1_sphere_normal_memLp ((hv a).of_le (by norm_num))) hνu hνv hnu hnv h.2⟩

#print axioms native_C1_sphere_normal_memLp
#print axioms native_C2_collar_trace_limits_unique
end Yamabe3.Analysis.SpherePolar
