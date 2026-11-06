import Yamabe3.Analysis.Sphere.NativeSphereEnergyGap
import Yamabe3.Analysis.SpectralDiagonalKernel
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The actual native H1 spectral Hilbert basis

Normalizing the existing energy eigenfunctions gives an orthonormal
family in the actual H1 completion. The real energy-to-L2 inclusion is
injective; the complete native L2 basis then proves that this family has
zero orthogonal complement. Its genuine Hilbert-basis isometry supplies
the converse weighted coefficient reconstruction, rather than assuming
that the finite energy Bessel inequality is sufficient.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT
open scoped Topology lp Manifold ContDiff Bundle RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.LeviCivitaData.Dirichlet
open Delaunay

private instance : ConnectedSpace (UnitSphere 2) := by
  apply isConnected_iff_connectedSpace.mp
  apply isConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

private theorem angular_energy_eigenvalue_nonneg (i : AngularIndex) :
    0 ≤ angularEigenvalue i := by
  rcases angularEigenvalue_zero_two_or_ge_six i with h | h | h
  · rw [h]
  · rw [h]; norm_num
  · linarith

def angularEnergyWeight (i : AngularIndex) : ℝ := Real.sqrt (1 + angularEigenvalue i)

theorem angularEnergyWeight_pos (i : AngularIndex) : 0 < angularEnergyWeight i :=
  Real.sqrt_pos.mpr (by linarith [angular_energy_eigenvalue_nonneg i])

theorem angularEnergyWeight_sq (i : AngularIndex) :
    angularEnergyWeight i ^ 2 = 1 + angularEigenvalue i :=
  Real.sq_sqrt (by linarith [angular_energy_eigenvalue_nonneg i])

def angularNormalizedEnergyMode (i : AngularIndex) : AngularH1 :=
  (angularEnergyWeight i)⁻¹ • angularEnergyMode i

theorem angularNormalizedEnergyMode_inner (i : AngularIndex) (u : AngularH1) :
    inner ℝ (angularNormalizedEnergyMode i) u =
      angularEnergyWeight i * inner ℝ (angularBasis i) (angularEmbedding u) := by
  rw [angularNormalizedEnergyMode, real_inner_smul_left, angularEnergyMode_inner]
  have hw := (angularEnergyWeight_pos i).ne'
  have he : (angularEnergyWeight i)⁻¹ * (1 + angularEigenvalue i) = angularEnergyWeight i := by
    rw [← angularEnergyWeight_sq]
    field_simp [hw]
  rw [← mul_assoc, he]

theorem angularNormalizedEnergyMode_orthonormal : Orthonormal ℝ angularNormalizedEnergyMode := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [angularNormalizedEnergyMode_inner, angularNormalizedEnergyMode, map_smul,
    angularEmbedding_energyMode, real_inner_smul_right,
    orthonormal_iff_ite.mp angularBasis.orthonormal i j]
  by_cases h : i = j
  · subst j
    simp [(angularEnergyWeight_pos i).ne']
  · simp [h]

/-- The actual native energy inclusion is faithful on the real round
sphere; connectedness is proved for that sphere, not added as an input. -/
theorem angularEmbedding_injective : Function.Injective angularEmbedding :=
  toDomainL2_injective MeasurableSet.univ

theorem angularNormalizedEnergyMode_orthogonal_eq_bot :
    (Submodule.span ℝ (range angularNormalizedEnergyMode))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  have hpair (i : AngularIndex) : inner ℝ (angularNormalizedEnergyMode i) u = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (mem_range_self i)) hu
  have hz : angularEmbedding u = 0 := by
    apply angularBasis.repr.injective
    ext i
    simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, HilbertBasis.repr_apply_apply]
    have hi := hpair i
    rw [angularNormalizedEnergyMode_inner] at hi
    exact (mul_eq_zero.mp hi).resolve_left (angularEnergyWeight_pos i).ne'
  apply angularEmbedding_injective
  rw [map_zero]
  exact hz

/-- A Hilbert basis of the actual completed native H1 space. -/
def angularEnergyBasis : HilbertBasis AngularIndex ℝ AngularH1 :=
  HilbertBasis.mkOfOrthogonalEqBot angularNormalizedEnergyMode_orthonormal
    angularNormalizedEnergyMode_orthogonal_eq_bot

theorem angularEnergyBasis_apply (i : AngularIndex) :
    angularEnergyBasis i = angularNormalizedEnergyMode i := by
  simp only [angularEnergyBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

theorem angularEnergyBasis_repr (u : AngularH1) (i : AngularIndex) :
    angularEnergyBasis.repr u i =
      angularEnergyWeight i * inner ℝ (angularBasis i) (angularEmbedding u) := by
  rw [HilbertBasis.repr_apply_apply, angularEnergyBasis_apply,
    angularNormalizedEnergyMode_inner]

/-- Actual converse reconstruction, with exact norm, in the existing H1
completion. The input is a genuine square-summable weighted family. -/
theorem angularEnergyBasis_synthesis_spec (c : SpectralSpace AngularIndex) :
    (∀ i, inner ℝ (angularBasis i) (angularEmbedding (angularEnergyBasis.repr.symm c)) =
      c i / angularEnergyWeight i) ∧ ‖angularEnergyBasis.repr.symm c‖ = ‖c‖ := by
  refine ⟨fun i => ?_, angularEnergyBasis.repr.symm.norm_map c⟩
  have h := angularEnergyBasis_repr (angularEnergyBasis.repr.symm c) i
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  apply (eq_div_iff (angularEnergyWeight_pos i).ne').mpr
  nlinarith only [h]

theorem angularEnergyBasis_hasSum_energy (u : AngularH1) :
    HasSum (fun i : AngularIndex => (1 + angularEigenvalue i) *
      (inner ℝ (angularBasis i) (angularEmbedding u)) ^ 2) (‖u‖ ^ 2) := by
  have h := angularEnergyBasis.hasSum_inner_mul_inner u u
  have he (i : AngularIndex) : inner ℝ u (angularEnergyBasis i) *
      inner ℝ (angularEnergyBasis i) u =
        (1 + angularEigenvalue i) * (inner ℝ (angularBasis i) (angularEmbedding u)) ^ 2 := by
    have hleft : inner ℝ u (angularEnergyBasis i) =
        angularEnergyWeight i * inner ℝ (angularBasis i) (angularEmbedding u) := by
      calc
        _ = inner ℝ (angularEnergyBasis i) u := real_inner_comm _ _
        _ = _ := by rw [angularEnergyBasis_apply, angularNormalizedEnergyMode_inner]
    have hright : inner ℝ (angularEnergyBasis i) u =
        angularEnergyWeight i * inner ℝ (angularBasis i) (angularEmbedding u) := by
      rw [angularEnergyBasis_apply, angularNormalizedEnergyMode_inner]
    rw [hleft, hright, ← angularEnergyWeight_sq]
    ring
  simpa only [he, real_inner_self_eq_norm_sq] using h

/-- A bounded diagonal acts on the actual H1 completion through its
proved Hilbert basis, not through a newly declared abstract Sobolev space. -/
def nativeAngularEnergyDiagonal (d : AngularIndex → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hd : ∀ i, |d i| ≤ B) : AngularH1 →L[ℝ] AngularH1 :=
  angularEnergyBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((spectralDiagonal d hB hd).comp
      angularEnergyBasis.repr.toLinearIsometry.toContinuousLinearMap)

theorem nativeAngularEnergyDiagonal_embedding_coefficient
    (d : AngularIndex → ℝ) {B : ℝ} (hB : 0 ≤ B) (hd : ∀ i, |d i| ≤ B)
    (u : AngularH1) (i : AngularIndex) :
    inner ℝ (angularBasis i) (angularEmbedding (nativeAngularEnergyDiagonal d hB hd u)) =
      d i * inner ℝ (angularBasis i) (angularEmbedding u) := by
  have he : angularEnergyBasis.repr (nativeAngularEnergyDiagonal d hB hd u) i =
      d i * angularEnergyBasis.repr u i := by
    change angularEnergyBasis.repr (angularEnergyBasis.repr.symm
      (spectralDiagonal d hB hd (angularEnergyBasis.repr u))) i = _
    rw [LinearIsometryEquiv.apply_symm_apply, spectralDiagonal_apply]
  rw [angularEnergyBasis_repr, angularEnergyBasis_repr] at he
  apply (mul_left_cancel₀ (angularEnergyWeight_pos i).ne')
  nlinarith only [he]

theorem nativeAngularEnergyDiagonal_apply_norm_le
    (d : AngularIndex → ℝ) {B : ℝ} (hB : 0 ≤ B) (hd : ∀ i, |d i| ≤ B)
    (u : AngularH1) : ‖nativeAngularEnergyDiagonal d hB hd u‖ ≤ B * ‖u‖ := by
  change ‖angularEnergyBasis.repr.symm
    (spectralDiagonal d hB hd (angularEnergyBasis.repr u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hb := mul_le_mul_of_nonneg_right (spectralDiagonal_norm_le d hB hd)
    (norm_nonneg (angularEnergyBasis.repr u))
  simpa only [LinearIsometryEquiv.norm_map] using hb

#print axioms angularEnergyBasis
#print axioms angularEnergyBasis_synthesis_spec
#print axioms angularEnergyBasis_hasSum_energy
#print axioms nativeAngularEnergyDiagonal_embedding_coefficient
#print axioms nativeAngularEnergyDiagonal_apply_norm_le

end Yamabe3.Analysis.SphereSpectrum
