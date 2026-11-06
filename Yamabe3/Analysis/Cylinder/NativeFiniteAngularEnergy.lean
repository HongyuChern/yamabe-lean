import Yamabe3.Analysis.Cylinder.NativeAngularTruncation
import Yamabe3.Analysis.Sphere.NativeSphereEnergyBasis

/-!
# Actual native gradient energy of finite angular functions

The same smooth representatives of the actual angular Hilbert basis are
used. Their finite scalar sum is identified with the corresponding
element of the actual native H1 completion by the faithful native L2
embedding. The completed energy identity therefore computes its genuine
induced-metric gradient integral, not merely a spectral proxy.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

open SphereSpectrum Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.LeviCivitaData.Dirichlet

theorem smooth_finiteAngular_sphere (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (t : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun θ : S => finiteAngular s q (t, θ)) := by
  apply contMDiff_finsetSum
  intro i hi
  exact ((contMDiff_const (c := q i t)).mul
    (smooth_angularRepresentative i)).congr (fun _ => rfl)

/-- The actual native scalar square integral of the existing finite
function has the exact Parseval value. No time regularity is required. -/
theorem integral_finiteAngular_square_eq_sum (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (t : ℝ) :
    (∫ θ : S, finiteAngular s q (t, θ) ^ 2 ∂(roundSphereMetric 2).volumeMeasure) =
      ∑ i ∈ s, q i t ^ 2 := by
  rw [integral_finiteAngular_square, ← real_inner_self_eq_norm_sq,
    angularBasis.orthonormal.inner_sum]
  simp only [conj_trivial, pow_two]

/-- The same finite native function has actual induced-sphere gradient
energy equal to the eigenvalue-weighted square sum. The proof uses the
true energy completion and its genuine integral on smooth tests. -/
theorem integral_finiteAngular_gradient_square (s : Finset AngularIndex)
    (q : AngularIndex → ℝ → ℝ) (t : ℝ) :
    (∫ θ : S, (roundSphereMetric 2).inner θ
      (sphereD.gradient (fun y : S => finiteAngular s q (t, y)) θ)
      (sphereD.gradient (fun y : S => finiteAngular s q (t, y)) θ)
        ∂(roundSphereMetric 2).volumeMeasure) =
      ∑ i ∈ s, angularEigenvalue i * q i t ^ 2 := by
  classical
  let ψ : EnergyTest sphereD univ :=
    ⟨(fun θ : S => finiteAngular s q (t, θ)), smooth_finiteAngular_sphere s q t,
      HasCompactSupport.of_compactSpace _, subset_univ _⟩
  let z : AngularH1 := ∑ i ∈ s, q i t • angularEnergyMode i
  have hz : angularEmbedding z = ∑ i ∈ s, q i t • angularBasis i := by
    simp only [z, map_sum, map_smul, angularEmbedding_energyMode]
  have htest : (toL2 sphereD univ (ψ : AngularH1) : S → ℝ) =ᵐ[
      (roundSphereMetric 2).volumeMeasure] (fun θ : S => finiteAngular s q (t, θ)) := by
    rw [toL2_coe]
    exact ψ.memLp.coeFn_toLp
  have hdom : (angularEmbedding (ψ : AngularH1) : S → ℝ) =ᵐ[
      (roundSphereMetric 2).volumeMeasure] (toL2 sphereD univ (ψ : AngularH1) : S → ℝ) := by
    simpa only [Measure.restrict_univ, angularEmbedding] using
      toDomainL2_ae (ψ : AngularH1)
  have hψ : (ψ : AngularH1) = z := by
    apply angularEmbedding_injective
    rw [hz]
    apply Lp.ext
    simpa only [Measure.restrict_univ] using
      (hdom.trans htest).trans (finiteAngular_ae s q t)
  have hpair (i : AngularIndex) (hi : i ∈ s) :
      inner ℝ (angularBasis i) (angularEmbedding z) = q i t := by
    rw [hz]
    exact angularBasis.orthonormal.inner_right_sum (fun j => q j t) hi
  have henergy : inner ℝ z z = ∑ i ∈ s, (1 + angularEigenvalue i) * q i t ^ 2 := by
    change inner ℝ (∑ i ∈ s, q i t • angularEnergyMode i) z = _
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left, angularEnergyMode_inner, hpair i hi]
    ring
  have hnorm : ‖angularEmbedding z‖ ^ 2 = ∑ i ∈ s, q i t ^ 2 := by
    rw [hz, ← real_inner_self_eq_norm_sq, angularBasis.orthonormal.inner_sum]
    simp only [conj_trivial, pow_two]
  calc
    _ = gradientEnergy sphereD univ (ψ : AngularH1) (ψ : AngularH1) := by
      rw [gradientEnergy_coe]
    _ = gradientEnergy sphereD univ z z := by rw [hψ]
    _ = inner ℝ z z - ‖angularEmbedding z‖ ^ 2 := by
      rw [gradientEnergy_apply, real_inner_self_eq_norm_sq (toL2 sphereD univ z)]
      congr 1
      exact congrArg (fun a : ℝ => a ^ 2) (norm_toDomainL2 MeasurableSet.univ z).symm
    _ = _ := by
      rw [henergy, hnorm, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

#print axioms smooth_finiteAngular_sphere
#print axioms integral_finiteAngular_square_eq_sum
#print axioms integral_finiteAngular_gradient_square

end Yamabe3.Analysis.SpherePolar
