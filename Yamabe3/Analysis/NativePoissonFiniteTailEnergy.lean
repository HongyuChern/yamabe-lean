import Yamabe3.Analysis.NativePoissonFiniteCollar

/-! The finite-tail version of the actual collar estimate. No total
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

theorem nativePoissonFiniteCollar_finite_energy (P : NativeHighPotential) (b : AngularH1)
    (s : Finset AngularIndex) :
    let u := nativePoissonFiniteCollar P b s
    let O := nativePolarTimeWindow (Ioo (-1) 1)
    ContDiffOn ℝ 2 u ({0}ᶜ : Set E) ∧
    IntegrableOn (fun x => u x^2) O ∧
    IntegrableOn (fun x => nativeCoordinateLaplacian u x^2) O ∧
      ((∫ x in O,u x^2)+(∫ x in O,nativeCoordinateLaplacian u x^2)) ≤
        (12000*Real.exp 2*(4+P.derivativeBound))*
          (∑ i ∈ s,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  let q := nativePoissonEntranceExtension P b
  have hq (i : AngularIndex) : ContDiff ℝ 2 (q i) := P.entranceExtension_C2 b i
  have hI (i : AngularIndex) := P.reflected_energy_spectral_bound b i
  have h0 := native_finitePhysical_collar_value_energy s q (fun i _ => hq i) (fun i _ => (hI i).1)
  have h2 := native_finitePhysical_collar_laplacian_energy s q (fun i _ => hq i)
    (fun i _ => (hI i).1) (fun i _ => (hI i).2.2.1)
  have hnon (i : AngularIndex) : 0 ≤ nativePoissonReflectedSecondEnergy P b i := by
    unfold nativePoissonReflectedSecondEnergy
    dsimp only
    positivity
  have hlower (i : AngularIndex) :
      (∫ t : ℝ,q i t^2) ≤ nativePoissonReflectedSecondEnergy P b i ∧
      ((∫ t : ℝ,deriv (deriv (q i)) t^2)+angularEnergyWeight i^4*(∫ t : ℝ,q i t^2)) ≤
        nativePoissonReflectedSecondEnergy P b i := by
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
    unfold nativePoissonReflectedSecondEnergy
    dsimp only
    change _ ≤ _ ∧ _ ≤ _
    dsimp only [q] at hv hd hdd hm hn
    constructor <;> nlinarith only [hv,hd,hdd,hm,hn]
  have hsum0 := Finset.sum_le_sum (fun i (_ : i ∈ s) => (hlower i).1)
  have hsum2 := Finset.sum_le_sum (fun i (_ : i ∈ s) => (hlower i).2)
  have hfinite : (∑ i ∈ s,nativePoissonReflectedSecondEnergy P b i) ≤
      (4000*(4+P.derivativeBound))*(∑ i ∈ s,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hI i).2.2.2)
  have he0 := h0.2.trans (mul_le_mul_of_nonneg_left hsum0 (Real.exp_pos 2).le)
  have he2 := h2.2.trans (mul_le_mul_of_nonneg_left hsum2 (by positivity))
  have he := mul_le_mul_of_nonneg_left hfinite (by positivity : 0 ≤ 3*Real.exp 2)
  refine ⟨finitePhysical_contDiffOn_offZero_C2 s q (fun i _ => hq i),h0.1,h2.1,?_⟩
  dsimp only [nativePoissonFiniteCollar]
  nlinarith only [he0,he2,he]

#print axioms nativePoissonFiniteCollar_finite_energy
end Yamabe3.Analysis.SpherePolar
