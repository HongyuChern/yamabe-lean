import Yamabe3.Analysis.NativeAngularC1Energy

/-! Genuine C1 angular data enter the native half-order trace scale.
The bound is the actual function/gradient energy on the round sphere. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace lp
namespace Yamabe3.Analysis.SphereSpectrum
open Poincare.Geometry.Riemannian.SpaceForm Yamabe3.Analysis.Delaunay

theorem nativeAngularWeightedSquare_one (f : AngularL2) (i : AngularIndex) :
    nativeAngularWeightedSquare 1 f i=(1+angularEigenvalue i)*(inner ℝ (angularBasis i) f)^2 := by
  unfold nativeAngularWeightedSquare
  rw [Real.rpow_one,mul_pow,angularEnergyWeight_sq]

theorem angular_C1_spectral_energy (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 f) :
    NativeAngularSpectralRegular 1 (continuousAngularL2 f hf.continuous) ∧
      (∑'i,nativeAngularWeightedSquare 1 (continuousAngularL2 f hf.continuous) i) ≤ angularC1Pair f f := by
  have hb (s : Finset AngularIndex) := angular_C1_finite_energy_bound f hf s
  simp_rw [←nativeAngularWeightedSquare_one] at hb
  exact ⟨summable_of_sum_le (fun _=>sq_nonneg _) hb,Real.tsum_le_of_sum_le (fun _=>sq_nonneg _) hb⟩

theorem nativeAngularSpectralRegular_mono {s t : ℝ} (hst : s ≤ t) {f : AngularL2}
    (hf : NativeAngularSpectralRegular t f) :
    NativeAngularSpectralRegular s f ∧
      (∑'i,nativeAngularWeightedSquare s f i) ≤ ∑'i,nativeAngularWeightedSquare t f i := by
  have hb (i : AngularIndex) : nativeAngularWeightedSquare s f i ≤ nativeAngularWeightedSquare t f i := by
    unfold nativeAngularWeightedSquare
    rw [mul_pow,mul_pow]
    have h := Real.rpow_le_rpow_of_exponent_le (angularEnergyWeight_one_le i) hst
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.rpow_nonneg (angularEnergyWeight_pos i).le _) h 2) (sq_nonneg _)
  have hs : NativeAngularSpectralRegular s f := Summable.of_nonneg_of_le (fun _=>sq_nonneg _) hb hf
  exact ⟨hs,Summable.tsum_le_tsum hb hs hf⟩

theorem angular_C1_half_trace (f : UnitSphere 2 → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) 1 f) :
    NativeAngularSpectralRegular (1/2) (continuousAngularL2 f hf.continuous) ∧
      (∑'i,nativeAngularWeightedSquare (1/2) (continuousAngularL2 f hf.continuous) i) ≤ angularC1Pair f f := by
  have h := angular_C1_spectral_energy f hf
  have hm := nativeAngularSpectralRegular_mono (by norm_num : (1/2:ℝ) ≤ 1) h.1
  exact ⟨hm.1,hm.2.trans h.2⟩

#print axioms angular_C1_spectral_energy
#print axioms nativeAngularSpectralRegular_mono
#print axioms angular_C1_half_trace
end Yamabe3.Analysis.SphereSpectrum
