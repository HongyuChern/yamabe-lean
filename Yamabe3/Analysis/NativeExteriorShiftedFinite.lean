import Yamabe3.Analysis.NativePoissonFiniteCollar
import Yamabe3.Analysis.NativeExteriorShiftedEnergy

/-! The actual finite-mode exterior collar energy at every scale, with the exact exp(4s) cost. No total
spectral summability is needed for this finite assertion, and the bound
retains exactly the frequencies in the chosen finite set. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeExteriorShiftedFinite_energy (P : NativeHighPotential) (b : AngularH1)
    (τ : ℝ) (s : Finset AngularIndex) :
    let u := finitePhysical s (nativeExteriorShiftedCoefficient P b τ)
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    ContDiffOn ℝ 2 u ({0}ᶜ : Set E) ∧
    IntegrableOn (fun x => u x^2) O ∧
    IntegrableOn (fun x => nativeCoordinateLaplacian u x^2) O ∧
      ((∫ x in O,u x^2)+(∫ x in O,nativeCoordinateLaplacian u x^2)) ≤
        (12000*Real.exp 2*Real.exp (4*τ)*(4+P.derivativeBound))*
          (∑ i ∈ s,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  let q := nativeExteriorShiftedCoefficient P b τ
  have hq (i : AngularIndex) : ContDiff ℝ 2 (q i) := nativeExteriorShiftedCoefficient_C2 P b τ i
  have hI (i : AngularIndex) := nativeExteriorShiftedEnergy_spectral_bound P b τ i
  have h0 := native_finitePhysical_collar_value_energy s q (fun i _ => hq i) (fun i _ => (hI i).1)
  have h2 := native_finitePhysical_collar_laplacian_energy s q (fun i _ => hq i)
    (fun i _ => (hI i).1) (fun i _ => (hI i).2.2.1)
  have hnon (i : AngularIndex) : 0 ≤ nativeExteriorShiftedEnergy P b τ i := by
    unfold nativeExteriorShiftedEnergy
    dsimp only
    positivity
  have hlower (i : AngularIndex) :
      (∫ t : ℝ,q i t^2) ≤ nativeExteriorShiftedEnergy P b τ i ∧
      ((∫ t : ℝ,deriv (deriv (q i)) t^2)+angularEnergyWeight i^4*(∫ t : ℝ,q i t^2)) ≤
        nativeExteriorShiftedEnergy P b τ i := by
    have hEig : 0 ≤ angularEigenvalue i := by
      rcases angularEigenvalue_zero_two_or_ge_six i with h | h | h <;> linarith
    have hw : 1 ≤ angularEnergyWeight i^4 := by
      rw [show angularEnergyWeight i^4=(angularEnergyWeight i^2)^2 by ring,angularEnergyWeight_sq]
      nlinarith only [hEig]
    have hv : 0 ≤ ∫ t : ℝ,q i t^2 := integral_nonneg (fun t => sq_nonneg (q i t))
    have hd : 0 ≤ ∫ t : ℝ,deriv (q i) t^2 := integral_nonneg (fun t => sq_nonneg (deriv (q i) t))
    have hdd : 0 ≤ ∫ t : ℝ,deriv (deriv (q i)) t^2 := integral_nonneg (fun t => sq_nonneg (deriv (deriv (q i)) t))
    have hm := mul_le_mul_of_nonneg_right hw hv
    have hn := mul_nonneg (sq_nonneg (angularEnergyWeight i)) hd
    unfold nativeExteriorShiftedEnergy
    dsimp only
    change _ ≤ _ ∧ _ ≤ _
    dsimp only [q] at hv hd hdd hm hn
    constructor <;> nlinarith only [hv,hd,hdd,hm,hn]
  have hsum0 := Finset.sum_le_sum (fun i (_ : i ∈ s) => (hlower i).1)
  have hsum2 := Finset.sum_le_sum (fun i (_ : i ∈ s) => (hlower i).2)
  have hfinite : (∑ i ∈ s,nativeExteriorShiftedEnergy P b τ i) ≤
      (4000*Real.exp (4*τ)*(4+P.derivativeBound))*(∑ i ∈ s,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hI i).2.2.2)
  have he0 := h0.2.trans (mul_le_mul_of_nonneg_left hsum0 (Real.exp_pos 2).le)
  have he2 := h2.2.trans (mul_le_mul_of_nonneg_left hsum2 (by positivity))
  have he := mul_le_mul_of_nonneg_left hfinite (by positivity : 0 ≤ 3*Real.exp 2)
  refine ⟨finitePhysical_contDiffOn_offZero_C2 s q (fun i _ => hq i),h0.1,h2.1,?_⟩
  nlinarith only [he0,he2,he]

#print axioms nativeExteriorShiftedFinite_energy
end Yamabe3.Analysis.SpherePolar
