import Yamabe3.Analysis.GreenRegularizedPairing
import Yamabe3.Analysis.GreenCorrection
import Yamabe3.Analysis.Green.NativeCutoffL2Limits

/-!
# Native inverse reciprocity and pointwise Green representation

The energy inverse is symmetric because its actual native bilinear form
is symmetric. Regularized chart tests then turn the previously proved
singular L2 pairing limit into pointwise representation identities. These
identities retain the actual residuals and continuous inverse representatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal InnerProductSpace

namespace Yamabe3.Analysis.GreenParametrix

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet
open Yamabe3.Parametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]

omit [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] in
/-- A possible singularity at a single point does not obstruct actual
Borel measurability. No completion-only representative is substituted. -/
theorem measurable_of_continuousOn_compl_singleton {f : M → ℝ} (p : M)
    (hf : ContinuousOn f ({p}ᶜ : Set M)) : Measurable f := by
  apply measurable_of_restrict_of_restrict_compl (measurableSet_singleton p)
  · have heq : (fun x : ↥({p} : Set M) => f x) = fun _ => f p := by
      funext x
      rw [show (x : M) = p from mem_singleton_iff.mp x.property]
    change Measurable (fun x : ↥({p} : Set M) => f x)
    rw [heq]
    exact measurable_const
  · exact hf.domRestrict.measurable

omit [IsManifold (𝓡 3) ∞ M] in
/-- The explicitly totalized native cutoff singularity is genuinely Borel
measurable, including its separately specified finite value at the pole. -/
theorem measurable_singular (e : OpenPartialHomeomorph E M)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (χ : ContDiffBump (0 : E)) (hχ : tsupport χ ⊆ e.source) :
    Measurable (singular e χ) :=
  measurable_of_continuousOn_compl_singleton (e 0)
    (contMDiffOn_singular e hei χ hχ).continuousOn

section Compact

variable [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Symmetry belongs to the actual completed native conformal form. -/
theorem closedConformalLaplacianForm_symm (g : RiemannianMetric 3 M)
    (v w : H1Zero g.leviCivitaData univ) :
    closedConformalLaplacianForm g v w = closedConformalLaplacianForm g w v := by
  rw [closedConformalLaplacianForm_apply, closedConformalLaplacianForm_apply]
  congr 1
  exact schrodingerForm_symm _ _ _ _ _ _ _ _

omit [CompactSpace M] [ConnectedSpace M] in
/-- The actual L2 source pairing is represented by the already constructed
continuous dual functional, with a.e. identifications made explicitly. -/
theorem closedL2Forcing_eq_integral_representative (g : RiemannianMetric 3 M)
    {F : M → ℝ} (hF : MemLp F 2 g.volumeMeasure)
    (w : H1Zero g.leviCivitaData univ) {U : M → ℝ}
    (hUae : U =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ w : M → ℝ)) :
    closedL2Forcing g (hF.toLp F) w = ∫ x, U x * F x ∂g.volumeMeasure := by
  rw [closedL2Forcing_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, hUae] with x hFx hUx
  change inner ℝ ((hF.toLp F) x) ((toL2 g.leviCivitaData univ w) x) = U x * F x
  rw [hFx, ← hUx]
  simp

/-- Reciprocity of the genuine inverse, expressed for the actual selected
representatives and residual functions. It is proved on the H1 completion,
so no illegal use of a Dirac functional is involved. -/
theorem closedL2Solution_reciprocity (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) {F₁ F₂ U₁ U₂ : M → ℝ}
    (hF₁ : MemLp F₁ 2 g.volumeMeasure) (hF₂ : MemLp F₂ 2 g.volumeMeasure)
    (hU₁ : U₁ =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ
      (closedConformalLaplacianL2Solution g hY (hF₁.toLp F₁)) : M → ℝ))
    (hU₂ : U₂ =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ
      (closedConformalLaplacianL2Solution g hY (hF₂.toLp F₂)) : M → ℝ)) :
    (∫ x, U₁ x * F₂ x ∂g.volumeMeasure) = ∫ x, U₂ x * F₁ x ∂g.volumeMeasure := by
  rw [← closedL2Forcing_eq_integral_representative g hF₂ _ hU₁,
    ← closedL2Forcing_eq_integral_representative g hF₁ _ hU₂,
    ← closedConformalLaplacianL2Solution_spec, ← closedConformalLaplacianL2Solution_spec]
  exact closedConformalLaplacianForm_symm _ _ _

/-- Native transposition for an actual inverse representative, with both
L2 representatives replaced by their proved a.e.-equal actual functions. -/
theorem L2Solution_representative_transposed (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) {F U : M → ℝ}
    (hF : MemLp F 2 g.volumeMeasure)
    (hUae : U =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ
      (closedConformalLaplacianL2Solution g hY (hF.toLp F)) : M → ℝ))
    (φ : EnergyTest g.leviCivitaData univ) :
    (∫ x, U x * (-g.leviCivitaData.laplacian φ x +
      (g.leviCivitaData.scalarCurvature x / 8) * φ x) ∂g.volumeMeasure) =
        ∫ x, F x * φ x ∂g.volumeMeasure := by
  calc
    _ = ∫ x, (-g.leviCivitaData.laplacian φ x +
        (g.leviCivitaData.scalarCurvature x / 8) * φ x) *
          (toL2 g.leviCivitaData univ
            (closedConformalLaplacianL2Solution g hY (hF.toLp F))) x ∂g.volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [hUae] with x hx
      rw [hx, mul_comm]
    _ = ∫ x, φ x * (hF.toLp F) x ∂g.volumeMeasure :=
      closedConformalLaplacianL2Solution_transposed g hY (hF.toLp F) φ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with x hx
      rw [hx, mul_comm]

/-- Pointwise representation of any continuous inverse representative by
the actual cutoff parametrix at a chosen pole. -/
theorem continuous_L2Solution_representation (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O : Set E} (hO : IsOpen O) (hOs : O ⊆ e.source)
    (hcoeff : ∀ x ∈ O, gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    (hρ0 : gE.pullbackVolumeDensity id 0 = 1)
    (hzero : fderiv ℝ (gE.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) (hχO : tsupport χ ⊆ O)
    {F U : M → ℝ} (hF : MemLp F 2 g.volumeMeasure) (hUc : Continuous U)
    (hUae : U =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ
      (closedConformalLaplacianL2Solution g hY (hF.toLp F)) : M → ℝ)) :
    4 * Real.pi * U (e 0) +
      (∫ x, U x * coordinateExtension e (nativeResidual gE χ) x ∂g.volumeMeasure) =
        ∫ x, F x * singular e χ x ∂g.volumeMeasure := by
  have hχs := hχO.trans hOs
  have hU : MemLp U 2 g.volumeMeasure :=
    (Lp.memLp (toL2 g.leviCivitaData univ
      (closedConformalLaplacianL2Solution g hY (hF.toLp F)))).ae_eq hUae.symm
  have hleft := tendsto_integral_native_regularizedP_L2 g gE e he hei hO hOs
    hcoeff hGauss hρ0 hzero χ hχO hU hUc.measurable hUc.continuousAt
  have hright := tendsto_integral_mul_regularized g e he hei χ hχs hF
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (L2Solution_representative_transposed g hY hF hUae
    (regularizedEnergyTest g e hei χ hχs hε)).symm

end Compact

/-- Testing an actual native point source at p by the genuine regularized
parametrix at a distinct pole gives its value at that second pole. -/
theorem native_pointSource_representation (g : RiemannianMetric 3 M)
    (gE : RiemannianMetric 3 E) (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {O : Set E} (hO : IsOpen O) (hOs : O ⊆ e.source)
    (hcoeff : ∀ x ∈ O, gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
    (hρ0 : gE.pullbackVolumeDensity id 0 = 1)
    (hzero : fderiv ℝ (gE.pullbackVolumeDensity id) 0 = 0)
    (χ : ContDiffBump (0 : E)) (hχO : tsupport χ ⊆ O)
    {p : M} (hp : p ≠ e 0) {G : M → ℝ}
    (hG : MemLp G 2 g.volumeMeasure) (hGm : Measurable G)
    (hGc : ContinuousAt G (e 0))
    (hsource : ∀ φ : EnergyTest g.leviCivitaData univ,
      (∫ x, (-g.leviCivitaData.laplacian φ x +
        (g.leviCivitaData.scalarCurvature x / 8) * φ x) * G x ∂g.volumeMeasure) =
          4 * Real.pi * φ p) :
    4 * Real.pi * G (e 0) +
      (∫ x, G x * coordinateExtension e (nativeResidual gE χ) x ∂g.volumeMeasure) =
        4 * Real.pi * singular e χ p := by
  have hχs := hχO.trans hOs
  have hleft := tendsto_integral_native_regularizedP_L2 g gE e he hei hO hOs
    hcoeff hGauss hρ0 hzero χ hχO hG hGm hGc
  have hright : Tendsto (fun ε : ℝ => 4 * Real.pi * regularized e χ ε p)
      (𝓝[>] 0) (𝓝 (4 * Real.pi * singular e χ p)) :=
    ((tendsto_regularized e χ hp).mono_left nhdsWithin_le_nhds).const_mul _
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hs := hsource (regularizedEnergyTest g e hei χ hχs hε)
  change (∫ x, (-g.leviCivitaData.laplacian (regularized e χ ε) x +
    (g.leviCivitaData.scalarCurvature x / 8) * regularized e χ ε x) * G x
      ∂g.volumeMeasure) = 4 * Real.pi * regularized e χ ε p at hs
  rw [← hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => mul_comm _ _

#print axioms measurable_of_continuousOn_compl_singleton
#print axioms measurable_singular
#print axioms closedConformalLaplacianForm_symm
#print axioms closedL2Forcing_eq_integral_representative
#print axioms closedL2Solution_reciprocity
#print axioms L2Solution_representative_transposed
#print axioms continuous_L2Solution_representation
#print axioms native_pointSource_representation

end Yamabe3.Analysis.GreenParametrix
