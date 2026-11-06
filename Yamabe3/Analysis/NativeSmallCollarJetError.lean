import Yamabe3.Analysis.NativeCollarJetPerturbation
import Yamabe3.Analysis.NativeC2GeometricError

/-! The normalized metric supplies the actual small second-order error
on the low-regularity H2 collar jet space. Uniformity precedes scale, pole
and jet. This is a local collar estimate, not yet a global half-end inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic

def nativeCollarGeometricErrorCLM (g : RiemannianMetric 3 E) (r : ℝ) :
    NativeCollarJet →L[ℝ] NativeCollarL2 :=
  nativeCollarJetPerturbationCLM (nativeScaledPrincipalError g r) (nativeScaledFirstError g r) (fun _ => 0)
    (fun i j => (contDiff_nativeScaledPrincipalError g r i j).continuous)
    (fun j => (contDiff_nativeScaledFirstError g r j).continuous) continuous_const

theorem nativeCollarGeometricError_C2_ae (g : RiemannianMetric 3 E) (r : ℝ) (u : nativeC2OffZero) :
    (nativeCollarGeometricErrorCLM g r (nativeC2CollarJetLinear u) : E → ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      nativeScaledGeometricError g r u.val := by
  have h := nativeCollarJetPerturbationCLM_ae (nativeScaledPrincipalError g r) (nativeScaledFirstError g r) (fun _ => 0)
    (fun i j => (contDiff_nativeScaledPrincipalError g r i j).continuous)
    (fun j => (contDiff_nativeScaledFirstError g r j).continuous) continuous_const (nativeC2CollarJetLinear u)
  have hm := nativeC2Collar_memLp u.property
  filter_upwards [h,eventually_all.mpr (fun i => eventually_all.mpr (fun j => (hm.2.2 i j).coeFn_toLp)),
    eventually_all.mpr (fun j => (hm.2.1 j).coeFn_toLp)] with x hx h2 h1
  change nativeCollarGeometricErrorCLM g r (nativeC2CollarJetLinear u) x=_
  unfold nativeCollarGeometricErrorCLM
  rw [hx]
  change (∑ i : Fin 3,∑ j : Fin 3,nativeScaledPrincipalError g r i j x*(nativeC2CollarSecond u.property i j : E → ℝ) x)+
    (∑ j : Fin 3,nativeScaledFirstError g r j x*(nativeC2CollarFirst u.property j : E → ℝ) x)+0*(nativeC2CollarValue u.property : E → ℝ) x=_
  have hh2 (i j : Fin 3) : (nativeC2CollarSecond u.property i j : E → ℝ) x=nativeCoordinateSecond i j u.val x := h2 i j
  have hh1 (j : Fin 3) : (nativeC2CollarFirst u.property j : E → ℝ) x=nativeCoordinateFirst j u.val x := h1 j
  simp only [hh2,hh1,nativeScaledGeometricError,secondOrderPerturbation,zero_mul,add_zero]
  rfl

theorem exists_uniform_small_native_collar_jet_error
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1)
    {τ : ℝ} (hτ : 0<τ) :
    ∃ δ : ℝ,0<δ ∧ ∀ r : ℝ,0≤r → r<δ → ∀ p ∈ Λ,∀ J : NativeCollarJet,
      ‖nativeCollarGeometricErrorCLM (g p) r J‖≤τ*‖J‖ := by
  obtain ⟨δ,hδ,hsmall⟩ := exists_uniform_small_native_geometric_error Λ g hB hρ (Real.exp_pos (1/2)) hτ
  refine ⟨δ,hδ,fun r hr hrδ p hp J => ?_⟩
  have hJ := hsmall r hr hrδ p hp
  have hsub : nativePoissonEntranceCollar ⊆ closedBall (0:E) (Real.exp (1/2)) := by
    intro x hx
    simpa only [mem_closedBall,dist_zero_right] using ((nativePolarTimeWindow_norm (1/2) x).mp hx).2.le
  have ha : ∀ x ∈ nativePoissonEntranceCollar,∀ i j,‖nativeScaledPrincipalError (g p) r i j x‖≤τ/91 := by
    intro x hx i j
    simpa only [norm_iteratedFDeriv_zero] using hJ.1 0 (by omega) x (hsub hx) i j
  have hb : ∀ x ∈ nativePoissonEntranceCollar,∀ j,‖nativeScaledFirstError (g p) r j x‖≤τ/91 := by
    intro x hx j
    simpa only [norm_iteratedFDeriv_zero] using hJ.2.1 0 (by omega) x (hsub hx) j
  have hh := nativeCollarJetPerturbationCLM_norm_le (nativeScaledPrincipalError (g p) r)
    (nativeScaledFirstError (g p) r) (fun _ => 0)
    (fun i j => (contDiff_nativeScaledPrincipalError (g p) r i j).continuous)
    (fun j => (contDiff_nativeScaledFirstError (g p) r j).continuous) continuous_const
    (by positivity : (0:ℝ)≤τ/91) ha hb (fun x hx => by simpa using (show (0:ℝ)≤τ/91 by positivity)) J
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : 13*(τ/91)≤τ) (norm_nonneg _))

#print axioms nativeCollarGeometricError_C2_ae
#print axioms exists_uniform_small_native_collar_jet_error
end Yamabe3.Analysis.SpherePolar
