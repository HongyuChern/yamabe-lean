/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Coordinates/Harmonic/WeakDivergence.lean

Uses the local divergence equation interface in the smooth forced problem with the
original metric and local source.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.GreenSmooth

/-!
# The actual native forced equation in coordinates

Both the retained volume density and the retained energy derivatives occur
in the coordinate identity. The source is an actual smooth function on the
manifold. Its integral is transported using the metric volume formula, not
an assumed coordinate forcing field.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis

open PoincareMT PoincareMT.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}

private theorem coordinate_memLp_of_continuousOn_compact
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContinuousOn f K) :
    MemLp f 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  exact MemLp.of_bound (hf.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx => hC x hx)

theorem integral_coordinate_test_smooth_source
    (F : M → ℝ) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    let f : EnergyTest D univ := EnergyTest.ofCoordinates e hei φ hφ hc
      (fun x hx => ⟨hKs (hOK (hs hx)), mem_univ (e x)⟩)
    (∫ y, f y * F y ∂g.volumeMeasure) =
      ∫ x in O, φ x * F (e x) * g.pullbackVolumeDensity e x := by
  dsimp only
  have hs' : tsupport φ ⊆ e.source ∩ e ⁻¹' (univ : Set M) :=
    fun x hx => ⟨hKs (hOK (hs hx)), mem_univ (e x)⟩
  let f : EnergyTest D univ := EnergyTest.ofCoordinates e hei φ hφ hc hs'
  have hfK : tsupport (f : M → ℝ) ⊆ e '' K :=
    (tsupport_coordinateExtension_subset_image e hc
      (hs'.trans inter_subset_left)).trans (image_mono (hs.trans hOK))
  calc
    _ = ∫ y in e '' K, f y * F y ∂g.volumeMeasure := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hy (hfK ht)), zero_mul]
    _ = ∫ x in K, f (e x) * F (e x) * g.pullbackVolumeDensity e x :=
      integral_compact_image_eq_pullback_density e he hei hK hKs
        (f.smooth.continuous.measurable.mul hF.continuous.measurable)
    _ = ∫ x in K, φ x * F (e x) * g.pullbackVolumeDensity e x := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      change f (e x) * F (e x) * g.pullbackVolumeDensity e x =
        φ x * F (e x) * g.pullbackVolumeDensity e x
      rw [show f (e x) = φ x from
        EnergyTest.ofCoordinates_apply e hei φ hφ hc hs' (hKs hx)]
    _ = _ := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hK.measurableSet hOK
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx.2 (hs ht)), zero_mul, zero_mul]

variable [CompactSpace M]

theorem weakSmoothForced_divergence_local
    {Ω : Set M} (V F : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (w : H1Zero D univ)
    (hweak : ∀ f : EnergyTest D univ, tsupport (f : M → ℝ) ⊆ Ω →
      (∫ y, (-D.laplacian f y + V y * f y) * toL2 D univ w y ∂g.volumeMeasure) =
        ∫ y, f y * F y ∂g.volumeMeasure)
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
      ∫ x in O, (g.pullbackVolumeDensity e x * F (e x) +
        (-g.pullbackVolumeDensity e x * V (e x)) * toL2 D univ w (e x)) * φ x := by
  have hs' : tsupport φ ⊆ e.source ∩ e ⁻¹' (univ : Set M) :=
    fun x hx => ⟨hKs (hOK (hs hx)), mem_univ (e x)⟩
  let f : EnergyTest D univ := EnergyTest.ofCoordinates e hei φ hφ hc hs'
  have hfs : tsupport (f : M → ℝ) ⊆ e '' tsupport φ :=
    tsupport_coordinateExtension_subset_image e hc (hs'.trans inter_subset_left)
  have hfΩ : tsupport (f : M → ℝ) ⊆ Ω :=
    (hfs.trans (image_mono hs)).trans hOΩ
  have hfK : tsupport (f : M → ℝ) ⊆ e '' K := hfs.trans (image_mono (hs.trans hOK))
  let hcompact : IsCompact (closure (univ : Set M)) := by simpa using isCompact_univ
  have hP : schrodingerForm D univ hcompact 1 V hV w (f : H1Zero D univ) =
      ∫ y, f y * F y ∂g.volumeMeasure := by
    rw [schrodingerForm_test_eq_integral]
    simpa only [neg_one_mul] using hweak f hfΩ
  have hpot : potentialForm D univ hcompact V hV w (f : H1Zero D univ) =
      ∫ y, V y * f y * toL2 D univ w y ∂g.volumeMeasure := by
    rw [potentialForm_symm]
    exact potentialForm_test_eq_integral _ _ _ _ _ _ _
  rw [schrodingerForm_apply, one_mul, hpot] at hP
  have hgradient : gradientEnergy D univ w (f : H1Zero D univ) =
      (∫ y, f y * F y ∂g.volumeMeasure) -
        (∫ y, V y * f y * toL2 D univ w y ∂g.volumeMeasure) := by linarith
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
    simp only [image_eq_zero_of_notMem_tsupport (fun ht => hx.2 (hs ht)), mul_zero, zero_mul]
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) K := by
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hKs hx)))
      (hD.mfderiv_injective (hKs hx))).1.continuousAt.continuousWithinAt
  have hFcoord : ContinuousOn (fun x => F (e x)) K :=
    hF.continuous.comp_continuousOn (e.continuousOn.mono hKs)
  have hVcoord : ContinuousOn (fun x => V (e x)) K :=
    hV.continuous.comp_continuousOn (e.continuousOn.mono hKs)
  have hiF : IntegrableOn (fun x => φ x * F (e x) * g.pullbackVolumeDensity e x) O :=
    ((hφ.continuous.continuousOn.mul hFcoord).mul hρ).integrableOn_compact hK |>.mono_set hOK
  have hiV : IntegrableOn (fun x => V (e x) * φ x * toL2 D univ w (e x) *
      g.pullbackVolumeDensity e x) O := by
    have ha := coordinate_memLp_of_continuousOn_compact hK
      ((hVcoord.mul hφ.continuous.continuousOn).mul hρ)
    have hw := g.memLp_pullback_on_compact e he hei (toL2 D univ w) hK hKs
    have hiK : IntegrableOn (fun x => (V (e x) * φ x * g.pullbackVolumeDensity e x) *
        toL2 D univ w (e x)) K := ha.integrable_mul hw
    apply (hiK.mono_set hOK).congr
    filter_upwards [] with x
    ring
  rw [coordinate_gradient_pairing_local e he hei hK hKs hOK w hφ hc hs,
    hgradient, integral_coordinate_test_smooth_source F hF e he hei hK hKs hOK hφ hc hs,
    hcoords, hrestrict, ← integral_sub hiF hiV]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

#print axioms integral_coordinate_test_smooth_source
#print axioms weakSmoothForced_divergence_local

end Yamabe3.Analysis
