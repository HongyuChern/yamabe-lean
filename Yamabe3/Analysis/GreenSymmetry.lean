import Yamabe3.Analysis.GreenReciprocity

/-!
# Symmetry of the actually constructed normalized Green functions

The proof uses the actual native point-source identity, the real L2 energy
inverse and the explicit chart parametrices. Another pole may lie inside a
cutoff support: the L1 kernel and L2 residual limits already cover that case.
No disjoint-support choice, distributional uniqueness axiom, or point-source
functional on H1 is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- The two actually corrected native parametrices are reciprocal away
from the diagonal. Every displayed input is retained by the proved native
construction theorem; no new mathematical obligation is inserted here. -/
theorem native_green_symmetry_of_construction (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (gEp gEq : RiemannianMetric 3 E) (ep eq : OpenPartialHomeomorph E M)
    (hep : ContMDiffOn (𝓡 3) (𝓡 3) ∞ ep ep.source)
    (hepi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ ep.symm ep.target)
    (heq : ContMDiffOn (𝓡 3) (𝓡 3) ∞ eq eq.source)
    (heqi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ eq.symm eq.target)
    {Op Oq : Set E} (hOp : IsOpen Op) (hOps : Op ⊆ ep.source)
    (hOq : IsOpen Oq) (hOqs : Oq ⊆ eq.source)
    (hcoeffp : ∀ x ∈ Op, gEp.euclideanCoefficients x = g.pullbackCoefficients ep x)
    (hcoeffq : ∀ x ∈ Oq, gEq.euclideanCoefficients x = g.pullbackCoefficients eq x)
    (hGaussp : ∀ x v : E, gEp.inner x x v = inner ℝ x v)
    (hGaussq : ∀ x v : E, gEq.inner x x v = inner ℝ x v)
    (hρp : gEp.pullbackVolumeDensity id 0 = 1)
    (hρq : gEq.pullbackVolumeDensity id 0 = 1)
    (hzerop : fderiv ℝ (gEp.pullbackVolumeDensity id) 0 = 0)
    (hzeroq : fderiv ℝ (gEq.pullbackVolumeDensity id) 0 = 0)
    (χp χq : ContDiffBump (0 : E))
    (hχp : tsupport χp ⊆ Op) (hχq : tsupport χq ⊆ Oq)
    (hFp : MemLp (coordinateExtension ep (nativeResidual gEp χp)) 2 g.volumeMeasure)
    (hFq : MemLp (coordinateExtension eq (nativeResidual gEq χq)) 2 g.volumeMeasure)
    (Up Uq : M → ℝ) (hUp : Continuous Up) (hUq : Continuous Uq)
    (hUpae : Up =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ
      (closedConformalLaplacianL2Solution g hY
        (hFp.toLp (coordinateExtension ep (nativeResidual gEp χp)))) : M → ℝ))
    (hUqae : Uq =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ
      (closedConformalLaplacianL2Solution g hY
        (hFq.toLp (coordinateExtension eq (nativeResidual gEq χq)))) : M → ℝ))
    (hsource : ∀ φ : EnergyTest g.leviCivitaData univ,
      (∫ x, (-g.leviCivitaData.laplacian φ x +
        (g.leviCivitaData.scalarCurvature x / 8) * φ x) *
          (singular ep χp x - Up x) ∂g.volumeMeasure) = 4 * Real.pi * φ (ep 0))
    (hpq : ep 0 ≠ eq 0) :
    singular ep χp (eq 0) - Up (eq 0) = singular eq χq (ep 0) - Uq (ep 0) := by
  have hχps := hχp.trans hOps
  have hUpL2 : MemLp Up 2 g.volumeMeasure :=
    (Lp.memLp (toL2 g.leviCivitaData univ
      (closedConformalLaplacianL2Solution g hY
        (hFp.toLp (coordinateExtension ep (nativeResidual gEp χp)))))).ae_eq hUpae.symm
  have hΦp : MemLp (singular ep χp) 2 g.volumeMeasure :=
    memLp_singular g ep hep hepi χp hχps
  have hGpMeas : Measurable (fun x => singular ep χp x - Up x) :=
    (measurable_singular ep hepi χp hχps).sub hUp.measurable
  have hGpCont : ContinuousAt (fun x => singular ep χp x - Up x) (eq 0) :=
    (contMDiffAt_singular ep hepi χp hχps hpq.symm).continuousAt.sub hUp.continuousAt
  have hGrep := native_pointSource_representation g gEq eq heq heqi hOq hOqs hcoeffq
    hGaussq hρq hzeroq χq hχq hpq (hΦp.sub hUpL2) hGpMeas hGpCont hsource
  have hUrep := continuous_L2Solution_representation g hY gEp ep hep hepi hOp hOps
    hcoeffp hGaussp hρp hzerop χp hχp hFq hUq hUqae
  have hrecip := closedL2Solution_reciprocity g hY hFp hFq hUpae hUqae
  have hIntegral : (∫ x, (singular ep χp x - Up x) *
      coordinateExtension eq (nativeResidual gEq χq) x ∂g.volumeMeasure) =
        (∫ x, coordinateExtension eq (nativeResidual gEq χq) x * singular ep χp x
          ∂g.volumeMeasure) -
          ∫ x, Up x * coordinateExtension eq (nativeResidual gEq χq) x
            ∂g.volumeMeasure := by
    calc
      _ = ∫ x, (singular ep χp x * coordinateExtension eq (nativeResidual gEq χq) x -
          Up x * coordinateExtension eq (nativeResidual gEq χq) x) ∂g.volumeMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => sub_mul _ _ _
      _ = (∫ x, singular ep χp x * coordinateExtension eq (nativeResidual gEq χq) x
          ∂g.volumeMeasure) -
            ∫ x, Up x * coordinateExtension eq (nativeResidual gEq χq) x ∂g.volumeMeasure :=
        integral_sub (hΦp.integrable_mul hFq) (hUpL2.integrable_mul hFq)
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_comm _ _
  simp only [Pi.sub_apply] at hGrep
  rw [hIntegral, hrecip] at hGrep
  apply mul_left_cancel₀ (show (4 : ℝ) * Real.pi ≠ 0 from mul_ne_zero (by norm_num) Real.pi_ne_zero)
  nlinarith [hGrep, hUrep]

#print axioms native_green_symmetry_of_construction

end Yamabe3.Analysis.GreenParametrix
