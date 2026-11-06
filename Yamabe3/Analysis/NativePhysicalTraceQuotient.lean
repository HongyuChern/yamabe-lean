import Yamabe3.Analysis.NativePhysicalCanonicalSphereTrace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The true physical trace quotient and its minimum energy lifting

The boundary space is the actual native H1 space modulo the kernel of the
proved physical sphere trace. Its norm is the quotient of that H1 norm.
It is complete, maps injectively to the actual physical sphere L2 space,
and has a canonical norm-preserving lifting given by the orthogonal
complement of the true trace kernel. That lifting attains the minimum H1
norm among all elements with the same actual boundary value.

The L2 range is identified algebraically with this quotient. We do not
identify its inherited L2 norm with the quotient norm, claim a bounded
right inverse from all L2, identify this space with a geometric H1/2
space, or assert that the trace kernel equals a domain H1-zero space.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology Manifold ContDiff InnerProductSpace

namespace Yamabe3.Analysis.HilbertTraceQuotient

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The kernel of a genuine bounded trace is closed. -/
instance kernelClosed (T : H →L[ℝ] F) : IsClosed (T.ker : Set H) :=
  T.isClosed_ker

abbrev Space (T : H →L[ℝ] F) := H ⧸ T.ker

def quotientMap (T : H →L[ℝ] F) : H →L[ℝ] Space T := T.ker.mkQL

/-- The boundary value is an actual element of the original target space. -/
def value (T : H →L[ℝ] F) : Space T →L[ℝ] F := T.ker.liftQL T le_rfl

theorem value_quotientMap (T : H →L[ℝ] F) (w : H) :
    value T (quotientMap T w) = T w := rfl

theorem value_injective (T : H →L[ℝ] F) : Function.Injective (value T) := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker (T.ker.liftQ T.toLinearMap le_rfl) = ⊥
  exact Submodule.ker_liftQ_eq_bot _ _ le_rfl le_rfl

/-- This is only an algebraic identification with the actual trace range;
the range's inherited target norm is not asserted to be the quotient norm. -/
def equivRange (T : H →L[ℝ] F) : Space T ≃ₗ[ℝ] T.range :=
  T.toLinearMap.quotKerEquivRange

theorem equivRange_coe (T : H →L[ℝ] F) (q : Space T) :
    (equivRange T q : F) = value T q := by
  induction q using Submodule.Quotient.induction_on with
  | _ w => rfl

/-- The actual quotient norm has an attained, linear, isometric lifting. -/
def minimumLift (T : H →L[ℝ] F) : Space T →ₗᵢ[ℝ] H :=
  T.kerᗮ.subtypeₗᵢ.comp T.ker.quotientEquivOrthogonal.toLinearIsometry

theorem minimumLift_mem_orthogonal (T : H →L[ℝ] F) (q : Space T) :
    minimumLift T q ∈ T.kerᗮ := (T.ker.quotientEquivOrthogonal q).property

theorem quotientMap_minimumLift (T : H →L[ℝ] F) (q : Space T) :
    quotientMap T (minimumLift T q) = q := by
  change (Submodule.Quotient.mk (T.ker.quotientEquivOrthogonal q).val : H ⧸ T.ker) = q
  exact Submodule.mk_quotientEquivOfIsCompl_apply T.ker.isCompl_orthogonal q

theorem trace_minimumLift (T : H →L[ℝ] F) (q : Space T) :
    T (minimumLift T q) = value T q := by
  have h := congrArg (value T) (quotientMap_minimumLift T q)
  exact h

theorem norm_minimumLift (T : H →L[ℝ] F) (q : Space T) :
    ‖minimumLift T q‖ = ‖q‖ := (minimumLift T).norm_map q

theorem minimumLift_norm_le (T : H →L[ℝ] F) (q : Space T) (w : H)
    (hw : T w = value T q) : ‖minimumLift T q‖ ≤ ‖w‖ := by
  have hq : quotientMap T w = q := value_injective T hw
  rw [norm_minimumLift, ← hq]
  exact Submodule.Quotient.norm_mk_le T.ker w

/-- The difference from every other lifting is orthogonal to the minimum
lifting, giving the genuine energy Pythagoras identity. -/
theorem norm_sq_lifting_eq (T : H →L[ℝ] F) (q : Space T) (w : H)
    (hw : T w = value T q) :
    ‖w‖ ^ 2 = ‖q‖ ^ 2 + ‖w - minimumLift T q‖ ^ 2 := by
  have hz : w - minimumLift T q ∈ T.ker := by
    change T (w - minimumLift T q) = 0
    rw [map_sub, hw, trace_minimumLift, sub_self]
  have hi : inner ℝ (w - minimumLift T q) (minimumLift T q) = 0 :=
    (T.ker.mem_orthogonal _).mp (minimumLift_mem_orthogonal T q) _ hz
  have hn := norm_add_sq_real (w - minimumLift T q) (minimumLift T q)
  rw [sub_add_cancel, hi, norm_minimumLift] at hn
  linarith only [hn]

theorem minimumLift_unique_of_norm (T : H →L[ℝ] F) (q : Space T) (w : H)
    (hw : T w = value T q) (hn : ‖w‖ = ‖q‖) : w = minimumLift T q := by
  have hsq := norm_sq_lifting_eq T q w hw
  rw [hn] at hsq
  have hz : ‖w - minimumLift T q‖ = 0 := by
    nlinarith only [hsq, norm_nonneg (w - minimumLift T q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The bound one is for the quotient energy norm, including the possible
zero boundary space. No unit operator norm is assumed for a trivial range. -/
theorem minimumLift_opNorm_le_one (T : H →L[ℝ] F) :
    ‖(minimumLift T).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖minimumLift T q‖ ≤ 1 * ‖q‖
  rw [norm_minimumLift, one_mul]

theorem completeSpace (T : H →L[ℝ] F) : CompleteSpace (Space T) := inferInstance

end Yamabe3.Analysis.HilbertTraceQuotient

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def physicalTraceQuotientH1NormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] physicalTraceQuotientH1NormedSpace

variable (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
  (e : OpenPartialHomeomorph E M)
  (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  {a b r C : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
  (hKs : sphereTraceAnnulus a b ⊆ e.source) (hC : 0 ≤ C)
  (hcoeff : ∀ θ : S, gE.euclideanCoefficients (r • (θ : E)) =
    g.pullbackCoefficients e (r • (θ : E)))
  (hGauss : ∀ (θ : S) (v : E), gE.inner (r • (θ : E)) (r • (θ : E)) v =
    inner ℝ (r • (θ : E)) v)
  (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (r • (θ : E)) ≤ C)

/-- The true native H1 quotient by the kernel of its actual physical trace. -/
abbrev NativePhysicalSphereBoundarySpace :=
  HilbertTraceQuotient.Space
    (nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ)

def nativePhysicalSphereBoundaryQuotient :=
  HilbertTraceQuotient.quotientMap
    (nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ)

def nativePhysicalSphereBoundaryValue :=
  HilbertTraceQuotient.value
    (nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ)

def nativePhysicalSphereMinimumLift :=
  HilbertTraceQuotient.minimumLift
    (nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ)

/-- The same actual physical boundary value, its quotient identity, norm
equality, minimality and uniqueness all refer to this one lifting. -/
theorem nativePhysicalSphereMinimumLift_spec
    (q : NativePhysicalSphereBoundarySpace g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ) :
    nativePhysicalSphereBoundaryQuotient g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ
      (nativePhysicalSphereMinimumLift g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ q) = q ∧
    nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ
      (nativePhysicalSphereMinimumLift g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ q) =
        nativePhysicalSphereBoundaryValue g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ q ∧
    ‖nativePhysicalSphereMinimumLift g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ q‖ = ‖q‖ ∧
    ∀ w : H1Zero g.leviCivitaData univ,
      nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ w =
        nativePhysicalSphereBoundaryValue g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ q →
      ‖nativePhysicalSphereMinimumLift g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ q‖ ≤ ‖w‖ ∧
      (‖w‖ = ‖q‖ →
        w = nativePhysicalSphereMinimumLift g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ q) := by
  let T := nativePhysicalSphereTraceCLM g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ
  exact ⟨HilbertTraceQuotient.quotientMap_minimumLift T q,
    HilbertTraceQuotient.trace_minimumLift T q, HilbertTraceQuotient.norm_minimumLift T q,
    fun w hw => ⟨HilbertTraceQuotient.minimumLift_norm_le T q w hw,
      HilbertTraceQuotient.minimumLift_unique_of_norm T q w hw⟩⟩

theorem nativePhysicalSphereBoundaryValue_injective :
    Function.Injective
      (nativePhysicalSphereBoundaryValue g gE e he hei ha hab hr hKs hC hcoeff hGauss hρ) :=
  HilbertTraceQuotient.value_injective _

theorem nativePhysicalSphereBoundarySpace_complete :
    CompleteSpace (NativePhysicalSphereBoundarySpace g gE e he hei ha hab hr hKs hC
      hcoeff hGauss hρ) := HilbertTraceQuotient.completeSpace _

#print axioms nativePhysicalSphereMinimumLift_spec
#print axioms nativePhysicalSphereBoundaryValue_injective
#print axioms nativePhysicalSphereBoundarySpace_complete

end Yamabe3.Analysis.SpherePolar
