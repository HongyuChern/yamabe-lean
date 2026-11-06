/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Coordinates/Harmonic/SmoothReplacement.lean
  PoincareLib/Geometry/Riemannian/Coordinates/Harmonic/WeakDivergence.lean
  PoincareLib/Geometry/Riemannian/Elliptic/Dirichlet/InteriorRegularity.lean

Retains the chart ellipticity verification and local regularity calculation in the
smooth-representative argument for the Green function.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.GreenContinuous
import Yamabe3.Analysis.GreenClassical
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.SmoothRepresentative
import PoincareLib.Analysis.Elliptic.Regularity.Eigenfunction

/-!
# Local smoothness for the native variable-potential equation

The fixed Euclidean regularity theorem accepts a smooth variable coefficient
`c(x)`. Its old native wrapper only handles a constant eigenvalue. This file
proves the native local transposed-to-coordinate equation for an arbitrary
smooth potential on the actual compact manifold, then invokes that proved
Euclidean regularity theorem. No regularity field is assumed for the energy
solution and no constant eigenvalue is manufactured.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

universe u

section LocalVariablePotential

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}

theorem coordinate_gradient_pairing_local
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K)
    (w : H1Zero D univ)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) w x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      gradientEnergy D univ w
        (EnergyTest.ofCoordinates (D := D) (Ω := univ) e hei φ hφ hc
          (fun x hx => ⟨hKs (hOK (hs hx)), mem_univ (e x)⟩) : H1Zero D univ) := by
  have hs' : tsupport φ ⊆ e.source ∩ e ⁻¹' (univ : Set M) :=
    fun x hx => ⟨hKs (hOK (hs hx)), mem_univ (e x)⟩
  have hcompact := coordinate_gradient_pairing e he hei hK hKs w hφ hc hs' (hs.trans hOK)
  rw [← hcompact]
  symm
  calc
    _ = ∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
        coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) w x *
        fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hK.measurableSet hOK
      intro x hx
      have hd (i : Fin n) : fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
          (fun ht => hx.2 (hs (tsupport_fderiv_apply_subset ℝ _ ht)))
      simp only [hd, mul_zero, Finset.sum_const_zero]
    _ = _ := by
      have hae : ∀ᵐ x ∂volume.restrict O, ∀ j : Fin n,
          localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) w x =
            coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) w x := by
        apply ae_all_iff.mpr
        intro j
        exact Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
          (by simpa only [one_smul] using Measure.restrict_mono hOK (le_refl volume)) _
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      simp only [hx]

variable [CompactSpace M]

/-- A local homogeneous native test equation becomes the genuine local
coordinate divergence equation with coefficient `-rho * V`. -/
theorem weakHomogeneous_divergence_local
    {Ω : Set M} (V : M → ℝ) (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (w : H1Zero D univ)
    (hweak : ∀ f : EnergyTest D univ, tsupport (f : M → ℝ) ⊆ Ω →
      (∫ y, (-D.laplacian f y + V y * f y) * toL2 D univ w y ∂g.volumeMeasure) = 0)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K) (hOΩ : e '' O ⊆ Ω)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) w x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in O, (-g.pullbackVolumeDensity e x * V (e x)) * toL2 D univ w (e x) * φ x := by
  have hs' : tsupport φ ⊆ e.source ∩ e ⁻¹' (univ : Set M) :=
    fun x hx => ⟨hKs (hOK (hs hx)), mem_univ (e x)⟩
  let f : EnergyTest D univ := EnergyTest.ofCoordinates e hei φ hφ hc hs'
  have hfs : tsupport (f : M → ℝ) ⊆ e '' tsupport φ :=
    tsupport_coordinateExtension_subset_image e hc (hs'.trans inter_subset_left)
  have hfΩ : tsupport (f : M → ℝ) ⊆ Ω :=
    (hfs.trans (image_mono hs)).trans hOΩ
  have hfK : tsupport (f : M → ℝ) ⊆ e '' K := hfs.trans (image_mono (hs.trans hOK))
  let hcompact : IsCompact (closure (univ : Set M)) := by simpa using isCompact_univ
  have hP : schrodingerForm D univ hcompact 1 V hV w (f : H1Zero D univ) = 0 := by
    rw [schrodingerForm_test_eq_integral]
    simpa only [neg_one_mul] using hweak f hfΩ
  have hpot : potentialForm D univ hcompact V hV w (f : H1Zero D univ) =
      ∫ y, V y * f y * toL2 D univ w y ∂g.volumeMeasure := by
    rw [potentialForm_symm]
    exact potentialForm_test_eq_integral _ _ _ _ _ _ _
  rw [schrodingerForm_apply, one_mul, hpot] at hP
  have hgradient : gradientEnergy D univ w (f : H1Zero D univ) =
      -(∫ y, V y * f y * toL2 D univ w y ∂g.volumeMeasure) := by linarith
  have hcoords : (∫ y, V y * f y * toL2 D univ w y ∂g.volumeMeasure) =
      ∫ x in K, V (e x) * φ x * toL2 D univ w (e x) * g.pullbackVolumeDensity e x := by
    have hh : tsupport ((f.mulSmooth V hV) : M → ℝ) ⊆ e '' K :=
      tsupport_mul_subset_right.trans hfK
    have h := integral_test_eq_compact_coordinates e he hei hK hKs
      (toL2 D univ w) (f.mulSmooth V hV) hh
    calc
      _ = ∫ x in K, (f.mulSmooth V hV) (e x) * toL2 D univ w (e x) *
          g.pullbackVolumeDensity e x := h
      _ = _ := by
        apply setIntegral_congr_fun hK.measurableSet
        intro x hx
        change V (e x) * f (e x) * toL2 D univ w (e x) * g.pullbackVolumeDensity e x = _
        rw [show f (e x) = φ x from EnergyTest.ofCoordinates_apply e hei φ hφ hc hs' (hKs hx)]
  have hrestrict : (∫ x in K, V (e x) * φ x * toL2 D univ w (e x) *
      g.pullbackVolumeDensity e x) =
      ∫ x in O, V (e x) * φ x * toL2 D univ w (e x) * g.pullbackVolumeDensity e x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hK.measurableSet hOK
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun ht => hx.2 (hs ht)),
      mul_zero, zero_mul]
  rw [coordinate_gradient_pairing_local e he hei hK hKs hOK w hφ hc hs,
    hgradient, hcoords, hrestrict, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

/-- Interior regularity for the actual native variable-potential equation.
The local weak derivatives and positive definite coefficient matrix are
constructed from the retained energy completion and metric. -/
theorem exists_smooth_representative_of_native_transposed
    (hn : 0 < n) {Ω : Set M} (hΩ : IsOpen Ω)
    (V : M → ℝ) (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (w : H1Zero D univ)
    (hweak : ∀ f : EnergyTest D univ, tsupport (f : M → ℝ) ⊆ Ω →
      (∫ y, (-D.laplacian f y + V y * f y) * toL2 D univ w y ∂g.volumeMeasure) = 0) :
    ∃ U : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω ∧
      U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D univ w : M → ℝ) := by
  apply exists_smooth_representative_of_local hΩ (toL2 D univ w)
  intro x hx
  obtain ⟨e, he, hei, K, hK, hKs, O, hO, hOK, hxO, hOΩ, -⟩ :=
    exists_precompact_coordinate_neighborhood (n := n) hΩ hx
  have hOs := hOK.trans hKs
  let p (i : Fin n) := localCoordinateDerivative (D := D) (Ω := univ)
    e he hei hK hKs hOK (EuclideanSpace.single i 1) w
  have huL2 := (g.memLp_pullback_on_compact e he hei (toL2 D univ w) hK hKs).mono_measure
    (Measure.restrict_mono hOK le_rfl)
  have hρ : ContDiffOn ℝ ∞ (g.pullbackVolumeDensity e) O := by
    intro y hy
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hOs hy)))
      (hD.mfderiv_injective (hOs hy))).1.contDiffWithinAt
  obtain ⟨U, hUs, hUae⟩ : ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ U O ∧ U =ᵐ[volume.restrict O] (fun y => toL2 D univ w (e y)) := by
    apply Poincare.Analysis.Elliptic.exists_smooth_representative hn hO
      (divergenceCoefficients g e) (fun y => -g.pullbackVolumeDensity e y * V (e y))
      (fun y => toL2 D univ w (e y)) (fun i y => p i y)
    · intro i j
      exact (contDiffOn_divergenceCoefficients e he hei i j).mono hOs
    · intro y hy
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        change divergenceCoefficients g e y j i = divergenceCoefficients g e y i j
        exact divergenceCoefficients_symm e he hei (hOs hy) j i
      · intro v hv
        have hv' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
          intro hz
          apply hv
          exact congrArg WithLp.ofLp hz
        have hpos := divergenceCoefficients_pos (g := g) e he hei (hOs hy)
          (WithLp.toLp 2 v) hv'
        simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
          Finset.mul_sum, PiLp.toLp_apply, mul_left_comm, mul_comm, mul_assoc] using hpos
    · exact hρ.neg.mul ((hV.comp_contMDiffOn he).contDiffOn.mono hOs)
    · intro K' _ hKO
      exact huL2.mono_measure (Measure.restrict_mono hKO le_rfl)
    · intro i K' _ hKO
      exact (Lp.memLp (p i)).mono_measure (Measure.restrict_mono hKO le_rfl)
    · intro i φ hφ hc hs
      exact localCoordinateDerivative_weak e he hei hK hKs hOK hO w i hφ hc hs
    · intro φ hφ hc hs
      exact weakHomogeneous_divergence_local V hV w hweak e he hei hK hKs hOK hOΩ hφ hc hs
  obtain ⟨H, hHs, hHae⟩ := g.exists_smooth_representative_on_coordinate_image
    e he hei hO hOs (toL2 D univ w) hUs hUae
  exact ⟨e '' O, e.isOpen_image_of_subset_source hO hOs, hxO, hOΩ, H, hHs, hHae⟩

end LocalVariablePotential

section CorrectedParametrix

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- A genuine L2 parametrix with its actual native point-source identity has
a continuous correction and a smooth homogeneous corrected representative
away from the pole. The point-source identity and off-pole smoothness of the
parametrix remain explicit inputs; positivity and symmetry are not asserted.

The proof of smoothness does not assume that the singular parametrix is H1.
At each point away from the pole, replace its germ by an actual compact
smooth function `H`. The energy element `H - w` has the required local
representative, so native variable-potential regularity applies legally.
-/
theorem parametrix_correction_exists_smooth (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M)
    (Φ F : M → ℝ) (hΦ : MemLp Φ 2 g.volumeMeasure)
    (hF : MemLp F 2 g.volumeMeasure)
    (hΦs : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ Φ ({p}ᶜ))
    (hparam : ∀ f : EnergyTest g.leviCivitaData univ,
      (∫ x, (-g.leviCivitaData.laplacian f x +
          (g.leviCivitaData.scalarCurvature x / 8) * f x) * Φ x ∂g.volumeMeasure) =
        4 * Real.pi * f p + ∫ x, f x * F x ∂g.volumeMeasure) :
    let w := closedConformalLaplacianL2Solution g hY (hF.toLp F)
    ∃ U : M → ℝ, Continuous U ∧ U =ᵐ[g.volumeMeasure] (toL2 g.leviCivitaData univ w : M → ℝ) ∧
      MemLp (fun x => Φ x - U x) 2 g.volumeMeasure ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => Φ x - U x) ({p}ᶜ) ∧
      (∀ x ∈ ({p}ᶜ : Set M),
        -g.leviCivitaData.laplacian (fun y => Φ y - U y) x +
          (g.leviCivitaData.scalarCurvature x / 8) * (Φ x - U x) = 0) ∧
      ∀ f : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian f x +
            (g.leviCivitaData.scalarCurvature x / 8) * f x) * (Φ x - U x) ∂g.volumeMeasure) =
          4 * Real.pi * f p := by
  classical
  dsimp only
  let D := g.leviCivitaData
  let Ω : Set M := {p}ᶜ
  have hΩ : IsOpen Ω := isClosed_singleton.isOpen_compl
  have hpΩ : p ∉ Ω := by simp [Ω]
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  let w := closedConformalLaplacianL2Solution g hY (hF.toLp F)
  obtain ⟨U, hUc, hUae⟩ := closedL2Solution_exists_continuous_representative g hY (hF.toLp F)
  let G : M → ℝ := fun x => Φ x - U x
  have hGcont : ContinuousOn G Ω := hΦs.continuousOn.sub hUc.continuousOn
  have hGmem : MemLp G 2 g.volumeMeasure :=
    hΦ.sub ((Lp.memLp (toL2 D univ w)).ae_eq hUae.symm)
  have hGtest (f : EnergyTest D univ) :
      (∫ x, (-D.laplacian f x + (D.scalarCurvature x / 8) * f x) * G x ∂g.volumeMeasure) =
        4 * Real.pi * f p := by
    have hbase := (parametrix_sub_L2Solution_test g hY p Φ F hΦ hF hparam).2 f
    calc
      _ = ∫ x, (-D.laplacian f x + (D.scalarCurvature x / 8) * f x) *
          (Φ x - toL2 D univ w x) ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [hUae] with x hx
        change _ * (Φ x - U x) = _
        rw [hx]
      _ = _ := hbase
  have hGsmooth : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ G Ω := by
    intro x hx
    obtain ⟨H, hHs, hHc, -, hHΦ⟩ := exists_compact_smooth_germ hΩ hΦs hx
    obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem (hΩ.mem_nhds hx) hHΦ)
    have hOΩ : O ⊆ Ω := fun y hy => (hOsub hy).1
    have hHΦO : EqOn H Φ O := fun y hy => (hOsub hy).2
    let Ht : EnergyTest D univ := ⟨H, hHs, hHc, subset_univ _⟩
    let v : H1Zero D univ := (Ht : H1Zero D univ) - w
    have hv : (toL2 D univ v : M → ℝ) =ᵐ[g.volumeMeasure]
        fun y => H y - toL2 D univ w y := by
      change ((toL2 D univ) ((Ht : H1Zero D univ) - w) : M → ℝ) =ᵐ[g.volumeMeasure] _
      rw [map_sub, toL2_coe]
      filter_upwards [Lp.coeFn_sub (testToL2 D univ Ht) (toL2 D univ w),
        Ht.memLp.coeFn_toLp] with y hsub hHt
      rw [hsub]
      simp only [Pi.sub_apply]
      rw [show testToL2 D univ Ht y = H y from hHt]
    have hvG : (toL2 D univ v : M → ℝ) =ᵐ[g.volumeMeasure.restrict O] G := by
      filter_upwards [ae_restrict_of_ae hv, ae_restrict_of_ae hUae,
        ae_restrict_mem hO.measurableSet] with y hvy hUy hy
      change toL2 D univ v y = Φ y - U y
      rw [hvy, hHΦO hy, hUy]
    have hvweak (f : EnergyTest D univ) (hs : tsupport (f : M → ℝ) ⊆ O) :
        (∫ y, (-D.laplacian f y + (D.scalarCurvature y / 8) * f y) *
          toL2 D univ v y ∂g.volumeMeasure) = 0 := by
      have hsP : tsupport (fun y => -D.laplacian f y + (D.scalarCurvature y / 8) * f y) ⊆ O :=
        (tsupport_add (f := fun y => -D.laplacian f y)
          (g := fun y => (D.scalarCurvature y / 8) * f y)).trans (union_subset
          (by change tsupport (-(D.laplacian f)) ⊆ O
              rw [tsupport_neg]
              exact (D.tsupport_laplacian_subset f).trans hs)
          (tsupport_mul_subset_right.trans hs))
      rw [integral_mul_eq_of_ae_eq_on hO hvG hsP]
      have hfp : f p = 0 := image_eq_zero_of_notMem_tsupport
        (fun hp => hpΩ (hOΩ (hs hp)))
      simpa only [hfp, mul_zero] using hGtest f
    obtain ⟨S, hSs, hSae⟩ := exists_smooth_representative_of_native_transposed
      (by norm_num : 0 < 3) hO (fun y => D.scalarCurvature y / 8)
      (D.contMDiff_scalarCurvature.div_const 8) v hvweak
    have hSG : EqOn S G O := Measure.eqOn_open_of_ae_eq (μ := g.volumeMeasure)
      (hSae.trans hvG) hO hSs.continuousOn (hGcont.mono hOΩ)
    have hGS : G =ᶠ[𝓝 x] S :=
      eventuallyEq_iff_exists_mem.mpr ⟨O, hO.mem_nhds hxO, fun y hy => (hSG hy).symm⟩
    exact ((hSs.contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq hGS).contMDiffWithinAt
  have hGpde : ∀ x ∈ Ω, -D.laplacian G x + (D.scalarCurvature x / 8) * G x = 0 := by
    apply native_conformalLaplacian_eq_zero_of_smooth_transposed D hΩ hGsmooth
    intro f
    let ff : EnergyTest D univ := ⟨f, f.smooth, f.hasCompactSupport, subset_univ _⟩
    have hfp : f p = 0 := image_eq_zero_of_notMem_tsupport (fun hp => hpΩ (f.support_subset hp))
    have h := hGtest ff
    change (∫ x, (-D.laplacian f x + (D.scalarCurvature x / 8) * f x) * G x ∂g.volumeMeasure) =
      4 * Real.pi * f p at h
    simpa only [hfp, mul_zero] using h
  exact ⟨U, hUc, hUae, hGmem, hGsmooth, hGpde, hGtest⟩

end CorrectedParametrix

#print axioms coordinate_gradient_pairing_local
#print axioms weakHomogeneous_divergence_local
#print axioms exists_smooth_representative_of_native_transposed
#print axioms parametrix_correction_exists_smooth

end Yamabe3.Analysis
