import Yamabe3.Analysis.Sphere.NativeSphereSpectralGap
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Basic
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.InteriorRegularity

/-!
# Actual angular eigenbasis with the proved native spectral gap

The basis is the genuine compact native resolvent eigenbasis on the full
round sphere.  Native elliptic regularity supplies smooth representatives,
and the proved lowering argument classifies its low modes.  The actual
Hilbert-basis reconstruction is retained; no spectrum certificate is input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.LeviCivitaData.Dirichlet

abbrev AngularL2 := Lp ℝ 2 ((roundSphereMetric 2).volumeMeasure.restrict univ)

abbrev AngularIndex := EigenIndex (roundSphereMetric 2).leviCivitaData univ

def angularBasis : HilbertBasis AngularIndex ℝ AngularL2 :=
  eigenbasis (roundSphereMetric 2).leviCivitaData univ (by decide) isOpen_univ
    (by simpa using (isCompact_univ : IsCompact (univ : Set (UnitSphere 2))))

def angularEigenvalue (i : AngularIndex) : ℝ :=
  eigenvalue (roundSphereMetric 2).leviCivitaData univ i

theorem exists_smooth_angular_eigenfunction (i : AngularIndex) :
    ∃ U : UnitSphere 2 → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ U ∧
      U =ᵐ[(roundSphereMetric 2).volumeMeasure] (angularBasis i : UnitSphere 2 → ℝ) ∧
      (∃ x, U x ≠ 0) ∧
      (∀ x, -(roundSphereMetric 2).leviCivitaData.laplacian U x = angularEigenvalue i * U x) := by
  let D := (roundSphereMetric 2).leviCivitaData
  have hc : IsCompact (closure (univ : Set (UnitSphere 2))) := by simpa using isCompact_univ
  let u := energyEigenfunction D univ (by decide) isOpen_univ hc i
  obtain ⟨U, hUs, hUae, hUP⟩ := exists_smooth_eigenfunction_representative D (by decide)
    isOpen_univ u (angularEigenvalue i)
    (energyEigenfunction_equation D univ (by decide) isOpen_univ hc i)
  have hdom : (toDomainL2 D univ u : UnitSphere 2 → ℝ) =ᵐ[(roundSphereMetric 2).volumeMeasure]
      (toL2 D univ u : UnitSphere 2 → ℝ) := by
    simpa only [Measure.restrict_univ] using toDomainL2_ae u
  have hvalue : toDomainL2 D univ u = angularBasis i :=
    toDomainL2_energyEigenfunction D univ (by decide) isOpen_univ hc i
  rw [hvalue] at hdom
  have hUae' : U =ᵐ[(roundSphereMetric 2).volumeMeasure] (toL2 D univ u : UnitSphere 2 → ℝ) := by
    simpa only [Measure.restrict_univ] using hUae
  have hae : U =ᵐ[(roundSphereMetric 2).volumeMeasure] (angularBasis i : UnitSphere 2 → ℝ) :=
    hUae'.trans hdom.symm
  refine ⟨U, contMDiffOn_univ.mp hUs, hae, ?_, fun x => hUP x (mem_univ x)⟩
  by_contra hzero
  have hUzero : ∀ x, U x = 0 := by simpa using hzero
  have hbzero : angularBasis i = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have hz : ∀ᵐ x ∂((roundSphereMetric 2).volumeMeasure.restrict univ),
        angularBasis i x = U x := ae_restrict_of_ae hae.symm
    filter_upwards [hz] with x hx
    change angularBasis i x = 0
    exact hx.trans (hUzero x)
  exact angularBasis.orthonormal.ne_zero i hbzero

theorem angularEigenvalue_zero_two_or_ge_six (i : AngularIndex) :
    angularEigenvalue i = 0 ∨ angularEigenvalue i = 2 ∨ 6 ≤ angularEigenvalue i := by
  obtain ⟨U, hU, _, hne, he⟩ := exists_smooth_angular_eigenfunction i
  exact native_eigenvalue_zero_two_or_ge_six (roundSphereMetric 2).leviCivitaData hU hne he

theorem angularBasis_zero_is_constant (i : AngularIndex) (hi : angularEigenvalue i = 0) :
    ∃ c : ℝ, (angularBasis i : UnitSphere 2 → ℝ) =ᵐ[(roundSphereMetric 2).volumeMeasure]
      fun _ => c := by
  obtain ⟨U, hU, hae, _, he⟩ := exists_smooth_angular_eigenfunction i
  obtain ⟨c, hc⟩ := native_harmonic_on_roundTwoSphere (roundSphereMetric 2).leviCivitaData hU
    (by simpa only [hi, zero_mul] using he)
  exact ⟨c, hae.symm.trans (Filter.Eventually.of_forall hc)⟩

theorem angularBasis_two_is_height (i : AngularIndex) (hi : angularEigenvalue i = 2) :
    ∃ a : Ambient 2, (angularBasis i : UnitSphere 2 → ℝ) =ᵐ[(roundSphereMetric 2).volumeMeasure]
      height a := by
  obtain ⟨U, hU, hae, _, he⟩ := exists_smooth_angular_eigenfunction i
  obtain ⟨a, ha⟩ := native_eigenvalue_two_is_height (roundSphereMetric 2).leviCivitaData hU
    (by simpa only [hi] using he)
  exact ⟨a, hae.symm.trans (Filter.Eventually.of_forall (congrFun ha))⟩

theorem angularBasis_reconstruct (f : AngularL2) :
    HasSum (fun i => inner ℝ (angularBasis i) f • angularBasis i) f := by
  simpa only [HilbertBasis.repr_apply_apply] using angularBasis.hasSum_repr f

#print axioms exists_smooth_angular_eigenfunction
#print axioms angularEigenvalue_zero_two_or_ge_six
#print axioms angularBasis_zero_is_constant
#print axioms angularBasis_two_is_height
#print axioms angularBasis_reconstruct

end Yamabe3.Analysis.SphereSpectrum
