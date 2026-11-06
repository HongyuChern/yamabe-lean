import Yamabe3.Analysis.NativeForcedHalfEndFiniteDifference
import Yamabe3.Analysis.NativeAngularProjections
import Yamabe3.Analysis.Cylinder.NativeAngularTruncation
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Compactness

/-! The actual low angular projection is finite and has a fixed smooth
representative map. Finiteness comes from the native compact resolvent,
not from an assumed dimension of the low space. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum Yamabe3.Analysis.SpherePolar
open Poincare.Geometry.Riemannian.SpaceForm

 theorem nativeLowIndex_finite : Set.Finite {i : AngularIndex | angularEigenvalue i < 6} := by
  have h := PoincareMT.LeviCivitaData.Dirichlet.finite_eigenvalue_le
    (roundSphereMetric 2).leviCivitaData univ (by decide) isOpen_univ
    (by simpa using (isCompact_univ : IsCompact (univ : Set (UnitSphere 2)))) 6
  apply h.subset
  intro i hi
  change angularEigenvalue i ≤ 6
  exact le_of_lt hi

def nativeLowIndexFinset : Finset AngularIndex := nativeLowIndex_finite.toFinset

@[simp] theorem mem_nativeLowIndexFinset (i : AngularIndex) :
    i ∈ nativeLowIndexFinset ↔ angularEigenvalue i < 6 := Set.Finite.mem_toFinset _

theorem nativeLowProjection_eq_finite (u : AngularL2) :
    nativeLowProjection u = finiteHilbertProjection angularBasis nativeLowIndexFinset u := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeLowProjection,nativeAngularProjection_coefficient,
    finiteHilbertProjection_coefficient,mem_nativeLowIndexFinset]

def nativeAngularRepresentativeMap (i : AngularIndex) : C(S,ℝ) :=
  ⟨angularRepresentative i,(smooth_angularRepresentative i).continuous⟩

def nativeLowRepresentativeCLM : AngularL2 →L[ℝ] C(S,ℝ) :=
  ∑ i ∈ nativeLowIndexFinset, (innerSL ℝ (angularBasis i)).smulRight (nativeAngularRepresentativeMap i)

theorem nativeLowRepresentativeCLM_apply (u : AngularL2) (x : S) :
    nativeLowRepresentativeCLM u x = ∑ i ∈ nativeLowIndexFinset,
      inner ℝ (angularBasis i) u*angularRepresentative i x := by
  simp only [nativeLowRepresentativeCLM,ContinuousLinearMap.sum_apply,ContinuousMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousMap.smul_apply,innerSL_apply_apply,
    smul_eq_mul,nativeAngularRepresentativeMap,ContinuousMap.coe_mk]

theorem nativeLowRepresentativeCLM_ae (u : AngularL2) :
    (nativeLowRepresentativeCLM u : S → ℝ) =ᵐ[(roundSphereMetric 2).volumeMeasure] (nativeLowProjection u : S → ℝ) := by
  have hh := finiteAngular_ae nativeLowIndexFinset (fun i (_ : ℝ) => inner ℝ (angularBasis i) u) 0
  change (fun x => ∑ i ∈ nativeLowIndexFinset, inner ℝ (angularBasis i) u*angularRepresentative i x)
    =ᵐ[(roundSphereMetric 2).volumeMeasure] ((finiteHilbertProjection angularBasis nativeLowIndexFinset u : AngularL2) : S → ℝ) at hh
  simpa only [← nativeLowRepresentativeCLM_apply,← nativeLowProjection_eq_finite] using hh

theorem nativeLowRepresentativeCLM_smooth (u : AngularL2) :
    ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (nativeLowRepresentativeCLM u : S → ℝ) := by
  have he : (nativeLowRepresentativeCLM u : S → ℝ) = fun x => ∑ i ∈ nativeLowIndexFinset,
      inner ℝ (angularBasis i) u*angularRepresentative i x := funext (nativeLowRepresentativeCLM_apply u)
  rw [he]
  apply contMDiff_finsetSum
  intro i _
  exact contMDiff_const.mul (smooth_angularRepresentative i)

#print axioms nativeLowIndex_finite
#print axioms nativeLowProjection_eq_finite
#print axioms nativeLowRepresentativeCLM_ae
#print axioms nativeLowRepresentativeCLM_smooth
end Yamabe3.Analysis.Delaunay
