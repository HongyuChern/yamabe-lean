import Yamabe3.Analysis.Sphere.NativeSphereHighModes
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.WeakDirichlet

/-!
# The native energy Poincare gap six after removing the low angular modes

Finite sums of the actual energy eigenfunctions give the Bessel inequality
in the genuine H1 completion.  Passing to the actual L2 Parseval limit and
using the proved low-mode classification gives the energy gap six.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.LeviCivitaData.Dirichlet

abbrev AngularH1 := H1Zero (roundSphereMetric 2).leviCivitaData univ

def angularEmbedding : AngularH1 →L[ℝ] AngularL2 :=
  toDomainL2 (roundSphereMetric 2).leviCivitaData univ

def angularEnergyMode (i : AngularIndex) : AngularH1 :=
  energyEigenfunction (roundSphereMetric 2).leviCivitaData univ (by decide) isOpen_univ
    (by simpa using (isCompact_univ : IsCompact (univ : Set (UnitSphere 2)))) i

theorem angularEmbedding_energyMode (i : AngularIndex) :
    angularEmbedding (angularEnergyMode i) = angularBasis i :=
  toDomainL2_energyEigenfunction (roundSphereMetric 2).leviCivitaData univ
    (by decide) isOpen_univ (by simpa using isCompact_univ) i

theorem angularEnergyMode_inner (i : AngularIndex) (u : AngularH1) :
    inner ℝ (angularEnergyMode i) u = (1 + angularEigenvalue i) *
      inner ℝ (angularBasis i) (angularEmbedding u) := by
  have h := energyEigenfunction_equation (roundSphereMetric 2).leviCivitaData univ
    (by decide) isOpen_univ (by simpa using isCompact_univ) i u
  change inner ℝ (angularEnergyMode i) u = (1 + angularEigenvalue i) * _ at h
  rw [← inner_toDomainL2 MeasurableSet.univ] at h
  change inner ℝ (angularEnergyMode i) u = (1 + angularEigenvalue i) *
    inner ℝ (angularEmbedding (angularEnergyMode i)) (angularEmbedding u) at h
  rwa [angularEmbedding_energyMode] at h

theorem finite_angular_energy_bound (u : AngularH1) (s : Finset AngularIndex) :
    (∑ i ∈ s, (1 + angularEigenvalue i) *
      (inner ℝ (angularBasis i) (angularEmbedding u)) ^ 2) ≤ ‖u‖ ^ 2 := by
  classical
  let c := fun i => inner ℝ (angularBasis i) (angularEmbedding u)
  let w : AngularH1 := ∑ i ∈ s, c i • angularEnergyMode i
  have hpair (i) (hi : i ∈ s) : inner ℝ (angularBasis i) (angularEmbedding w) = c i := by
    simp only [w, map_sum, map_smul, angularEmbedding_energyMode, inner_sum, real_inner_smul_right]
    have hb (j) : inner ℝ (angularBasis i) (angularBasis j) = if i = j then 1 else 0 :=
      orthonormal_iff_ite.mp angularBasis.orthonormal i j
    simp_rw [hb]
    simp [hi]
  have hleft : inner ℝ u w = ∑ i ∈ s, (1 + angularEigenvalue i) * (c i) ^ 2 := by
    simp only [w, inner_sum, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (angularEnergyMode i) u, angularEnergyMode_inner]
    change c i * ((1 + angularEigenvalue i) * c i) = _
    ring
  have hself : inner ℝ w w = ∑ i ∈ s, (1 + angularEigenvalue i) * (c i) ^ 2 := by
    change inner ℝ (∑ i ∈ s, c i • angularEnergyMode i) w = _
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_left, angularEnergyMode_inner, hpair i hi]
    ring
  have hpos : 0 ≤ inner ℝ (u - w) (u - w) := real_inner_self_nonneg
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm u w,
    hleft, hself, real_inner_self_eq_norm_sq] at hpos
  dsimp only [c] at hpos
  linarith

theorem native_high_angular_energy_gap (u : AngularH1)
    (hmean : (∫ x, angularEmbedding u x ∂(roundSphereMetric 2).volumeMeasure) = 0)
    (hfirst : ∀ a : Ambient 2,
      (∫ x, height a x * angularEmbedding u x ∂(roundSphereMetric 2).volumeMeasure) = 0) :
    6 * ‖toL2 (roundSphereMetric 2).leviCivitaData univ u‖ ^ 2 ≤
      gradientEnergy (roundSphereMetric 2).leviCivitaData univ u u := by
  classical
  let f := angularEmbedding u
  let c := fun i => inner ℝ (angularBasis i) f
  have hpoint (i : AngularIndex) : 7 * (c i) ^ 2 ≤ (1 + angularEigenvalue i) * (c i) ^ 2 := by
    by_cases hi : 6 ≤ angularEigenvalue i
    · exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    · have hz := angular_coefficient_zero_of_low_moments f hmean hfirst i (lt_of_not_ge hi)
      change c i = 0 at hz
      rw [hz]
      norm_num
  have hfin (s : Finset AngularIndex) : 7 * ∑ i ∈ s, (c i) ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum (fun i _ => hpoint i)).trans (finite_angular_energy_bound u s)
  have hs : HasSum (fun i : AngularIndex => (c i) ^ 2) (‖f‖ ^ 2) := by
    have h := angularBasis.hasSum_inner_mul_inner f f
    have he (i : AngularIndex) : inner ℝ f (angularBasis i) *
        inner ℝ (angularBasis i) f = (c i) ^ 2 := by
      dsimp only [c]
      rw [real_inner_comm (angularBasis i) f]
      ring
    simpa only [he, real_inner_self_eq_norm_sq] using h
  have hlim : 7 * ‖f‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    apply le_of_tendsto (hs.mul_left 7)
    exact Filter.Eventually.of_forall (fun s => by simpa only [Finset.mul_sum] using hfin s)
  change 7 * ‖toDomainL2 (roundSphereMetric 2).leviCivitaData univ u‖ ^ 2 ≤ ‖u‖ ^ 2 at hlim
  rw [norm_toDomainL2 MeasurableSet.univ] at hlim
  rw [gradientEnergy_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  linarith

#print axioms finite_angular_energy_bound
#print axioms native_high_angular_energy_gap

end Yamabe3.Analysis.SphereSpectrum
