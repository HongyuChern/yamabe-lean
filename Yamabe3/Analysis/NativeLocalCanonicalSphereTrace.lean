import Yamabe3.Analysis.NativeCanonicalSphereTrace
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Weighted.Multiplication
import PoincareLib.Geometry.Manifold.PartitionOfUnity.CompactSupport

/-!
# The actual trace of a canonical energy element with a local smooth representative

The smooth representative may be singular away from the selected sphere.
A genuine smooth cutoff is constructed around that actual compact sphere,
inside the open set on which the representative is smooth. Multiplication
is the existing native energy multiplier. Its actual L2 representative is
the pointwise product, and its value trace equals the original trace when
the cutoff is one on the sphere. The globally smooth product can therefore
be identified with the same energy element before taking its sphere trace.

No ambient almost-everywhere identity is restricted to the sphere. No
global smoothness of a punctured representative, kernel-surjectivity,
normal derivative, or weak-conormal identification is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory Filter UniformSpace
open scoped Manifold ContDiff Topology

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet SpherePolar

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

private def localCanonicalSphereTraceH1NormedSpace (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] localCanonicalSphereTraceH1NormedSpace

/-- The actual native H1 trace is unchanged by the existing energy
multiplier whenever that smooth multiplier equals one on the actual sphere. -/
theorem nativeSphereTraceCLM_energyMulSmooth_of_sphere_one
    (g : RiemannianMetric 3 M) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hχone : ∀ θ : S, χ (e (r • (θ : E))) = 1)
    (w : H1Zero g.leviCivitaData univ) :
    nativeSphereTraceCLM g e he hei ha hab hr hKs
      (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ) χ hχ w) =
        nativeSphereTraceCLM g e he hei ha hab hr hKs w := by
  induction w using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((nativeSphereTraceCLM g e he hei ha hab hr hKs).continuous.comp
          (energyMulSmooth g.leviCivitaData univ
            (by simpa using isCompact_univ) χ hχ).continuous)
        (nativeSphereTraceCLM g e he hei ha hab hr hKs).continuous
  | ih φ =>
      rw [energyMulSmooth_coe, nativeSphereTraceCLM_coe, nativeSphereTraceCLM_coe]
      apply Lp.ext
      filter_upwards [nativeSphereTestTraceLinear_ae g e r
        (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) (φ.mulSmooth χ hχ),
        nativeSphereTestTraceLinear_ae g e r
          (fun θ => hKs (radial_mem_sphereTraceAnnulus ha hr θ)) φ] with θ h₁ h₂
      rw [h₁, h₂]
      change χ (e (r • (θ : E))) * φ (e (r • (θ : E))) = φ (e (r • (θ : E)))
      rw [hχone θ, one_mul]

/-- The same energy multiplier represents the literal product in the
actual original native volume, including on nonsmooth completed elements. -/
theorem native_energyMulSmooth_toL2_ae
    (g : RiemannianMetric 3 M) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (w : H1Zero g.leviCivitaData univ) :
    (toL2 g.leviCivitaData univ
      (energyMulSmooth g.leviCivitaData univ
        (by simpa using isCompact_univ) χ hχ w) : M → ℝ) =ᵐ[g.volumeMeasure]
      (fun x => χ x * toL2 g.leviCivitaData univ w x) := by
  let hc : IsCompact (closure (univ : Set M)) := by simpa using isCompact_univ
  have heq := toDomainL2_energyMulSmooth (D := g.leviCivitaData)
    isOpen_univ hc χ hχ w
  have hlocal : (toL2 g.leviCivitaData univ
      (energyMulSmooth g.leviCivitaData univ hc χ hχ w) : M → ℝ)
      =ᵐ[g.volumeMeasure.restrict univ]
        (fun x => χ x * toL2 g.leviCivitaData univ w x) := by
    filter_upwards [toDomainL2_ae
      (energyMulSmooth g.leviCivitaData univ hc χ hχ w),
      domainMulL2_ae isOpen_univ hc χ hχ.continuous
        (toDomainL2 g.leviCivitaData univ w), toDomainL2_ae w] with x h₁ h₂ h₃
    rw [heq] at h₁
    exact h₁.symm.trans (h₂.trans (congrArg (fun y : ℝ => χ x * y) h₃))
  simpa only [Measure.restrict_univ] using hlocal

/-- A smooth representative only on an open neighborhood of the actual
sphere has the literal sphere trace of the same completed energy element.
The cutoff is produced internally from the actual compact sphere. -/
theorem nativeSphereTraceCLM_of_locally_smooth_representative
    (g : RiemannianMetric 3 M) (w : H1Zero g.leviCivitaData univ)
    {U : Set M} (hU : IsOpen U) (W : M → ℝ)
    (hW : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ W U)
    (hae : W =ᵐ[g.volumeMeasure.restrict U]
      (toL2 g.leviCivitaData univ w : M → ℝ))
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : r ∈ Icc a b)
    (hKs : sphereTraceAnnulus a b ⊆ e.source)
    (hSphereU : ∀ θ : S, e (r • (θ : E)) ∈ U) :
    (nativeSphereTraceCLM g e he hei ha hab hr hKs w : S → ℝ) =ᵐ[angularVolume]
      nativeSphereRestriction e r W := by
  have hm : Continuous (fun θ : S => e (r • (θ : E))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hrθ : r • (θ : E) ∈ e.source :=
      hKs (radial_mem_sphereTraceAnnulus ha hr θ)
    have hc : ContinuousAt (fun q : S => r • (q : E)) θ :=
      ((continuous_const_smul r).comp continuous_subtype_val).continuousAt
    exact ContinuousAt.comp (f := fun q : S => r • (q : E))
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hrθ)) hc
  let K : Set M := range (fun θ : S => e (r • (θ : E)))
  have hK : IsCompact K := isCompact_range hm
  have hKU : K ⊆ U := by
    rintro x ⟨θ, rfl⟩
    exact hSphereU θ
  obtain ⟨χ, hχ, _, hχU, _, hχnear⟩ :=
    exists_contMDiff_cutoff_of_isCompact (n := 3) hK hU hKU
  have hχone (θ : S) : χ (e (r • (θ : E))) = 1 := by
    simpa only [Pi.one_apply] using (hχnear _ ⟨θ, rfl⟩).self_of_nhds
  let V : M → ℝ := fun x => χ x * W x
  have hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V := by
    apply contMDiff_of_tsupport
    intro x hx
    exact hχ.contMDiffAt.mul
      (hW.contMDiffAt (hU.mem_nhds (hχU (tsupport_mul_subset_left hx))))
  let v := energyMulSmooth g.leviCivitaData univ
    (by simpa using isCompact_univ) χ hχ w
  have hprod := native_energyMulSmooth_toL2_ae g χ hχ w
  have haeU : ∀ᵐ x ∂g.volumeMeasure, x ∈ U →
      W x = toL2 g.leviCivitaData univ w x := (ae_restrict_iff' hU.measurableSet).mp hae
  have hVae : V =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ v : M → ℝ) := by
    filter_upwards [haeU, hprod] with x hx hp
    change χ x * W x = _
    rw [hp]
    by_cases hxU : x ∈ U
    · rw [hx hxU]
    · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hxU (hχU ht))
      rw [hz, zero_mul, zero_mul]
  have htrace := nativeSphereTraceCLM_of_smooth_representative
    g v V hV hVae e he hei ha hab hr hKs
  have hsame := nativeSphereTraceCLM_energyMulSmooth_of_sphere_one
    g e he hei ha hab hr hKs χ hχ hχone w
  change nativeSphereTraceCLM g e he hei ha hab hr hKs v =
    nativeSphereTraceCLM g e he hei ha hab hr hKs w at hsame
  rw [hsame] at htrace
  filter_upwards [htrace] with θ hθ
  exact hθ.trans (by
    change χ (e (r • (θ : E))) * W (e (r • (θ : E))) = W (e (r • (θ : E)))
    rw [hχone θ, one_mul])

#print axioms nativeSphereTraceCLM_energyMulSmooth_of_sphere_one
#print axioms native_energyMulSmooth_toL2_ae
#print axioms nativeSphereTraceCLM_of_locally_smooth_representative

end Yamabe3.Analysis
