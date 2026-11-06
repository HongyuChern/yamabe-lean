import Yamabe3.Analysis.NativeC2CollarNormalBound

/-! Genuine restrictions vanish along volume C1/H2 zero limits.
These are the closed-trace estimates used to identify limits; no pointwise
restriction of a volume-a.e. representative is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar

theorem nativeCoordinateFirst_sub {u v : E → ℝ}
    (hu : ContDiffOn ℝ 1 u ({0}ᶜ : Set E)) (hv : ContDiffOn ℝ 1 v ({0}ᶜ : Set E))
    (j : Fin 3) {x : E} (hx : x ≠ 0) :
    nativeCoordinateFirst j (fun y => u y-v y) x = nativeCoordinateFirst j u x-nativeCoordinateFirst j v x := by
  have ho : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  unfold nativeCoordinateFirst
  rw [fderiv_fun_sub ((hu.contDiffAt (ho.mem_nhds hx)).differentiableAt (by norm_num))
    ((hv.contDiffAt (ho.mem_nhds hx)).differentiableAt (by norm_num))]
  rfl

theorem nativeCoordinateSecond_sub {u v : E → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set E)) (hv : ContDiffOn ℝ 2 v ({0}ᶜ : Set E))
    (k j : Fin 3) {x : E} (hx : x ≠ 0) :
    nativeCoordinateSecond k j (fun y => u y-v y) x = nativeCoordinateSecond k j u x-nativeCoordinateSecond k j v x := by
  have ho : IsOpen ({0}ᶜ : Set E) := isClosed_singleton.isOpen_compl
  have he : nativeCoordinateFirst j (fun y => u y-v y) =ᶠ[𝓝 x]
      (fun y => nativeCoordinateFirst j u y-nativeCoordinateFirst j v y) := by
    filter_upwards [ho.mem_nhds hx] with y hy
    exact nativeCoordinateFirst_sub (hu.of_le (by norm_num)) (hv.of_le (by norm_num)) j hy
  have hp : ContDiffOn ℝ 1 (nativeCoordinateFirst j u) {0}ᶜ :=
    (hu.fderiv_of_isOpen ho (by norm_num)).clm_apply contDiffOn_const
  have hq : ContDiffOn ℝ 1 (nativeCoordinateFirst j v) {0}ᶜ :=
    (hv.fderiv_of_isOpen ho (by norm_num)).clm_apply contDiffOn_const
  unfold nativeCoordinateSecond
  rw [he.fderiv_eq,fderiv_fun_sub ((hp.contDiffAt (ho.mem_nhds hx)).differentiableAt (by norm_num))
    ((hq.contDiffAt (ho.mem_nhds hx)).differentiableAt (by norm_num))]
  rfl

theorem native_C1_collar_restriction_tendsto_zero {ι : Type*} {l : Filter ι}
    (u : ι → E → ℝ) (hu : ∀ a,ContDiffOn ℝ 1 (u a) ({0}ᶜ : Set E))
    (henergy : Tendsto (fun a => ∫ x in nativePoissonEntranceCollar,
      u a x^2+∑ j : Fin 3,nativeCoordinateFirst j (u a) x^2) l (𝓝 0)) :
    Tendsto (fun a => ∫ θ : S,u a (θ:E)^2 ∂angularVolume) l (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_native_C1_collar_value_trace_bound
  have h := henergy.const_mul C
  simp only [mul_zero] at h
  exact squeeze_zero (fun a => integral_nonneg (fun θ => sq_nonneg (u a (θ:E))))
    (fun a => hbound (u a) (hu a)) h

theorem native_C2_collar_normal_tendsto_zero {ι : Type*} {l : Filter ι}
    (u : ι → E → ℝ) (hu : ∀ a,ContDiffOn ℝ 2 (u a) ({0}ᶜ : Set E))
    (henergy : Tendsto (fun a => ∑ j : Fin 3,∫ x in nativePoissonEntranceCollar,
      nativeCoordinateFirst j (u a) x^2+∑ k : Fin 3,nativeCoordinateSecond k j (u a) x^2) l (𝓝 0)) :
    Tendsto (fun a => ∫ θ : S,(fderiv ℝ (u a) (θ:E) (θ:E))^2 ∂angularVolume) l (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_native_C2_collar_normal_trace_bound
  have h := henergy.const_mul C
  simp only [mul_zero] at h
  exact squeeze_zero (fun a => integral_nonneg (fun θ => sq_nonneg _))
    (fun a => hbound (u a) (hu a)) h

#print axioms nativeCoordinateSecond_sub
#print axioms native_C1_collar_restriction_tendsto_zero
#print axioms native_C2_collar_normal_tendsto_zero
end Yamabe3.Analysis.SpherePolar
