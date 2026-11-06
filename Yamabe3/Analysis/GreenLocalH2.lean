/-
Copyright (c) 2026 The PoincareLib contributors.
SPDX-License-Identifier: Apache-2.0

Adapted from PoincareLib at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
  PoincareLib/Geometry/Riemannian/Elliptic/Dirichlet/DivergenceEquation.lean

Adapts the coordinate-gradient pairing to general L2 forcing, using convergence in the
retained gradient energy.
See MODIFICATIONS.md and NOTICE.md for the source links and notices.
-/

import Yamabe3.Analysis.GreenCorrection
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.DivergenceEquation
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.LocalChart
import PoincareLib.Analysis.Elliptic.Regularity.InteriorH2

/-!
# Local native H2 regularity with general L2 forcing

The coordinate weak derivatives here are the actual continuous extensions of
coordinate derivatives on the native energy completion. The coordinate
pairing identity is proved without the eigenfunction hypothesis used by the
fixed upstream `DivergenceEquation` wrapper. Its density proof follows that
upstream argument with the retained gradient-energy limit instead of an
assumed eigenvalue equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory UniformSpace Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

section GeneralNative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

private theorem local_memLp_of_continuousOn_compact
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContinuousOn F K) :
    MemLp F 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  exact MemLp.of_bound (hF.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx => hC x hx)

/-- Coordinate divergence pairings of every completed native H1 element
agree with its actual gradient energy. No equation is assumed. -/
theorem coordinate_gradient_pairing
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (w : H1Zero D Ω)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω)
    (hφK : tsupport φ ⊆ K) :
    (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) w x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      gradientEnergy D Ω w
        (EnergyTest.ofCoordinates (D := D) e hei φ hφ hc hs : H1Zero D Ω) := by
  let T (j : Fin n) := coordinateDerivative (D := D) (Ω := Ω) e he hei hK hKs
    (EuclideanSpace.single j 1)
  let ψ (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :=
    divergenceCoefficients g e x i j * fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ (i j : Fin n) : MemLp (ψ i j) 2 (volume.restrict K) :=
    local_memLp_of_continuousOn_compact hK
      (((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono
        hKs).mul (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn))
  have hint (v : H1Zero D Ω) (i j : Fin n) :
      Integrable (fun x => T j v x * ψ i j x) (volume.restrict K) :=
    (Lp.memLp (T j v)).integrable_mul (hψ i j)
  have heq (v : H1Zero D Ω) :
      (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j v x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∑ i, ∑ j, ∫ x in K, T j v x * ψ i j x := by
    calc
      _ = ∫ x in K, ∑ i, ∑ j, T j v x * ψ i j x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          dsimp [ψ]
          ring
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint v i j))]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hint v i j)
  obtain ⟨f, hf, -⟩ := exists_energyTest_approximation w
  have hlim (i j : Fin n) := Poincare.Analysis.Elliptic.tendsto_integral_mul_L2
    ((T j).continuous.continuousAt.tendsto.comp hf) (hψ i j)
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hlim i j
  let h : EnergyTest D Ω := EnergyTest.ofCoordinates e hei φ hφ hc hs
  have hh : tsupport (h : M → ℝ) ⊆ e '' K :=
    (tsupport_coordinateExtension_subset_image e hc (hs.trans inter_subset_left)).trans
      (image_mono hφK)
  have hseq (k : ℕ) :
      (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j (f k) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ y, g.inner y (D.gradient (f k) y) (D.gradient h y) ∂g.volumeMeasure := by
    rw [integral_gradient_eq_compact_coordinates e he hei hK hKs (f k) h hh]
    have hae : ∀ᵐ x ∂volume.restrict K, ∀ j : Fin n,
        T j (f k) x = fderiv ℝ (fun y => f k (e y)) x (EuclideanSpace.single j 1) := by
      apply ae_all_iff.mpr
      intro j
      change (coordinateDerivative (D := D) (Ω := Ω) e he hei hK hKs _ (f k : H1Zero D Ω) :
        EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict K] _
      rw [coordinateDerivative_coe]
      exact EnergyTest.coordinateDerivativeL2_ae e he hK hKs _ (f k)
    apply integral_congr_ae
    filter_upwards [hae, ae_restrict_mem hK.measurableSet] with x hx hxK
    simp_rw [hx]
    have hd := (EnergyTest.ofCoordinates_comp_eventuallyEq (D := D)
      e hei φ hφ hc hs (hKs hxK)).fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (fun y => h (e y)) x = fderiv ℝ φ x at hd
    rw [← hd, ← density_mul_inner_gradient_eq_sum_divergenceCoefficients e he hei
      (f k) h (hKs hxK), mul_comm]
  have hsum' : Tendsto (fun k =>
      ∫ y, g.inner y (D.gradient (f k) y) (D.gradient h y) ∂g.volumeMeasure) atTop
      (𝓝 (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j w x *
        fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    rw [heq]
    exact hsum.congr' (Eventually.of_forall fun k => (heq (f k)).symm.trans (hseq k))
  have henergy : Tendsto (fun k =>
      ∫ y, g.inner y (D.gradient (f k) y) (D.gradient h y) ∂g.volumeMeasure) atTop
      (𝓝 (gradientEnergy D Ω w (h : H1Zero D Ω))) := by
    have ht := ((gradientEnergy D Ω).flip (h : H1Zero D Ω)).continuous.continuousAt.tendsto.comp hf
    simpa only [Function.comp_def, ContinuousLinearMap.flip_apply, gradientEnergy_coe] using ht
  exact tendsto_nhds_unique hsum' henergy

/-- General L2 forcing gives the genuine density-weighted coordinate
equation; it is not restricted to an eigenfunction right-hand side. -/
theorem weakForced_divergence_compact
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (w : H1Zero D Ω) (F : Lp ℝ 2 g.volumeMeasure)
    (hforcing : ∀ h : EnergyTest D Ω,
      gradientEnergy D Ω w (h : H1Zero D Ω) = ∫ y, h y * F y ∂g.volumeMeasure)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω)
    (hφK : tsupport φ ⊆ K) :
    (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) w x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in K, φ x * F (e x) * g.pullbackVolumeDensity e x := by
  rw [coordinate_gradient_pairing e he hei hK hKs w hφ hc hs hφK, hforcing]
  let h : EnergyTest D Ω := EnergyTest.ofCoordinates e hei φ hφ hc hs
  have hh : tsupport (h : M → ℝ) ⊆ e '' K :=
    (tsupport_coordinateExtension_subset_image e hc (hs.trans inter_subset_left)).trans
      (image_mono hφK)
  rw [integral_test_eq_compact_coordinates e he hei hK hKs F h hh]
  apply setIntegral_congr_fun hK.measurableSet
  intro x hx
  dsimp only
  rw [show h (e x) = φ x from EnergyTest.ofCoordinates_apply e hei φ hφ hc hs (hKs hx)]

theorem weakForced_divergence_local
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K) (hOΩ : e '' O ⊆ Ω)
    (w : H1Zero D Ω) (F : Lp ℝ 2 g.volumeMeasure)
    (hforcing : ∀ h : EnergyTest D Ω,
      gradientEnergy D Ω w (h : H1Zero D Ω) = ∫ y, h y * F y ∂g.volumeMeasure)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) w x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in O, (g.pullbackVolumeDensity e x * F (e x)) * φ x := by
  have hs' : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω :=
    fun x hx => ⟨hKs (hOK (hs hx)), hOΩ (mem_image_of_mem e (hs hx))⟩
  have hcompact := weakForced_divergence_compact e he hei hK hKs w F hforcing
    hφ hc hs' (hs.trans hOK)
  have hleft : (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) w x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
        localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) w x *
        fderiv ℝ φ x (EuclideanSpace.single i 1) := by
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
  have hright : (∫ x in K, φ x * F (e x) * g.pullbackVolumeDensity e x) =
      ∫ x in O, φ x * F (e x) * g.pullbackVolumeDensity e x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hK.measurableSet hOK
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun ht => hx.2 (hs ht)), zero_mul]
  rw [hleft, hright] at hcompact
  rw [hcompact]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

theorem memLp_density_mul_pullback_on_compact
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (F : Lp ℝ 2 g.volumeMeasure) :
    MemLp (fun x => g.pullbackVolumeDensity e x * F (e x)) 2 (volume.restrict K) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) K := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hKs hx)))
      (hD.mfderiv_injective (hKs hx))).1.continuousAt.continuousWithinAt
  have hF := g.memLp_pullback_on_compact e he hei F hK hKs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hρ
  apply hF.of_le_mul (c := C)
    ((hρ.aestronglyMeasurable hK.measurableSet).mul hF.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)

/-- Native H1 weak solutions with general L2 Laplace forcing have genuine
local coordinate W2,2 regularity. The weak derivatives and coefficients are
constructed from the metric and energy completion, rather than supplied as
free regularity data. -/
theorem exists_coordinate_H2_of_weakForced [NeZero n]
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K) (hO : IsOpen O) (hOΩ : e '' O ⊆ Ω)
    (w : H1Zero D Ω) (F : Lp ℝ 2 g.volumeMeasure)
    (hforcing : ∀ h : EnergyTest D Ω,
      gradientEnergy D Ω w (h : H1Zero D Ω) = ∫ y, h y * F y ∂g.volumeMeasure)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ O) :
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧
      Poincare.Analysis.Sobolev.Euclidean.MemWkp 2 2
        (fun y => toL2 D Ω w (e y)) W := by
  let p (i : Fin n) := localCoordinateDerivative (D := D) (Ω := Ω)
    e he hei hK hKs hOK (EuclideanSpace.single i 1) w
  have huL2 := (g.memLp_pullback_on_compact e he hei (toL2 D Ω w) hK hKs).mono_measure
    (Measure.restrict_mono hOK le_rfl)
  have hfL2 := (memLp_density_mul_pullback_on_compact e he hei hK hKs F).mono_measure
    (Measure.restrict_mono hOK le_rfl)
  apply Poincare.Analysis.Elliptic.exists_memWkp_two_of_weakEquation hO
    (divergenceCoefficients g e) (fun y => toL2 D Ω w (e y))
    (fun y => g.pullbackVolumeDensity e y * F (e y)) (fun i y => p i y)
  · intro i j
    exact (contDiffOn_divergenceCoefficients e he hei i j).mono (hOK.trans hKs)
  · intro y hy
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      change divergenceCoefficients g e y j i = divergenceCoefficients g e y i j
      exact divergenceCoefficients_symm e he hei (hKs (hOK hy)) j i
    · intro v hv
      have hv' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
        intro hz
        apply hv
        exact congrArg WithLp.ofLp hz
      have hpos := divergenceCoefficients_pos (g := g) e he hei (hKs (hOK hy))
        (WithLp.toLp 2 v) hv'
      simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        Finset.mul_sum, PiLp.toLp_apply, mul_left_comm, mul_comm, mul_assoc] using hpos
  · intro K' _ hKO
    exact huL2.mono_measure (Measure.restrict_mono hKO le_rfl)
  · intro i K' _ hKO
    exact (Lp.memLp (p i)).mono_measure (Measure.restrict_mono hKO le_rfl)
  · intro K' _ hKO
    exact hfL2.mono_measure (Measure.restrict_mono hKO le_rfl)
  · intro i φ hφ hc hs
    exact localCoordinateDerivative_weak e he hei hK hKs hOK hO w i hφ hc hs
  · intro φ hφ hc hs
    exact weakForced_divergence_local e he hei hK hKs hOK hOΩ w F hforcing hφ hc hs
  · exact hx

end GeneralNative

section ClosedThreeDimensional

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- The retained-volume L2 representative of `F − (R/8)w`, formed using
the actual continuous smooth multiplier on the energy completion. -/
def closedLaplacianForcing (g : RiemannianMetric 3 M)
    (F : Lp ℝ 2 g.volumeMeasure) (w : H1Zero g.leviCivitaData univ) :
    Lp ℝ 2 g.volumeMeasure :=
  F - (1 / 8 : ℝ) • toL2 g.leviCivitaData univ
    (energyMulSmooth g.leviCivitaData univ (by simpa using isCompact_univ)
      g.leviCivitaData.scalarCurvature g.leviCivitaData.contMDiff_scalarCurvature w)

/-- The constructed L2 right-hand side is the claimed native pointwise
expression almost everywhere; the smooth multiplier is not an opaque
substitute for multiplication by scalar curvature. -/
theorem closedLaplacianForcing_ae (g : RiemannianMetric 3 M)
    (F : Lp ℝ 2 g.volumeMeasure) (w : H1Zero g.leviCivitaData univ) :
    (closedLaplacianForcing g F w : M → ℝ) =ᵐ[g.volumeMeasure]
      fun x => F x - (g.leviCivitaData.scalarCurvature x / 8) *
        toL2 g.leviCivitaData univ w x := by
  let hcompact : IsCompact (closure (univ : Set M)) := by simpa using isCompact_univ
  let V := g.leviCivitaData.scalarCurvature
  let hw := energyMulSmooth g.leviCivitaData univ hcompact V
    g.leviCivitaData.contMDiff_scalarCurvature w
  have heq := toDomainL2_energyMulSmooth (D := g.leviCivitaData) isOpen_univ hcompact V
    g.leviCivitaData.contMDiff_scalarCurvature w
  have ha := domainMulL2_ae (g := g) isOpen_univ hcompact V
    g.leviCivitaData.continuous_scalarCurvature (toDomainL2 g.leviCivitaData univ w)
  rw [← heq] at ha
  have hprod : (toL2 g.leviCivitaData univ hw : M → ℝ) =ᵐ[g.volumeMeasure]
      fun x => V x * toL2 g.leviCivitaData univ w x := by
    have hh : (toL2 g.leviCivitaData univ hw : M → ℝ) =ᵐ[g.volumeMeasure.restrict univ]
        fun x => V x * toL2 g.leviCivitaData univ w x := by
      filter_upwards [toDomainL2_ae hw, toDomainL2_ae w, ha] with x h₁ h₂ h₃
      rw [← h₁, h₃, h₂]
    simpa only [Measure.restrict_univ] using hh
  filter_upwards [Lp.coeFn_sub F ((1 / 8 : ℝ) • toL2 g.leviCivitaData univ hw),
    Lp.coeFn_smul (1 / 8 : ℝ) (toL2 g.leviCivitaData univ hw), hprod]
    with x hsub hsmul hmul
  change (F - (1 / 8 : ℝ) • toL2 g.leviCivitaData univ hw) x = _
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmul]
  dsimp [V]
  ring

theorem closedL2Solution_gradient_forcing (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure)
    (f : EnergyTest g.leviCivitaData univ) :
    let w := closedConformalLaplacianL2Solution g hY F
    gradientEnergy g.leviCivitaData univ w (f : H1Zero g.leviCivitaData univ) =
      ∫ x, f x * closedLaplacianForcing g F w x ∂g.volumeMeasure := by
  dsimp only
  have hw := closedConformalLaplacianL2Solution_spec g hY F
    (f : H1Zero g.leviCivitaData univ)
  rw [closedConformalLaplacianForm_apply, closedL2Forcing_apply] at hw
  change (1 / 8 : ℝ) * schrodingerForm g.leviCivitaData univ
    (by simpa using isCompact_univ) 8 g.leviCivitaData.scalarCurvature
    g.leviCivitaData.contMDiff_scalarCurvature
    (closedConformalLaplacianL2Solution g hY F) (f : H1Zero g.leviCivitaData univ) = _ at hw
  rw [schrodingerForm_apply, potentialForm_apply, toL2_coe] at hw
  rw [integral_test_mul]
  simp only [closedLaplacianForcing, inner_sub_left, real_inner_smul_left]
  linarith

/-- At every point, the genuinely constructed L2-forced solution has a
native coordinate H2 neighborhood. Only the original positive-Yamabe
hypothesis is used to construct this solution. -/
theorem closedL2Solution_exists_coordinate_H2 (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure) (x : M) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M,
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      ∃ W : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W ∧ W ⊆ e.source ∧ x ∈ e '' W ∧
        Poincare.Analysis.Sobolev.Euclidean.MemWkp 2 2
          (fun y => toL2 g.leviCivitaData univ
            (closedConformalLaplacianL2Solution g hY F) (e y)) W := by
  obtain ⟨e, he, hei, K, hK, hKs, O, hO, hOK, hxO, hOΩ, -⟩ :=
    exists_precompact_coordinate_neighborhood (n := 3) isOpen_univ (mem_univ x)
  obtain ⟨y, hy, hyx⟩ := hxO
  let w := closedConformalLaplacianL2Solution g hY F
  obtain ⟨W, hW, hyW, hWO, hH2⟩ := exists_coordinate_H2_of_weakForced
    e he hei hK hKs hOK hO hOΩ w (closedLaplacianForcing g F w)
    (closedL2Solution_gradient_forcing g hY F) hy
  exact ⟨e, he, hei, W, hW, hWO.trans (hOK.trans hKs), ⟨y, hyW, hyx⟩, hH2⟩

#print axioms coordinate_gradient_pairing
#print axioms weakForced_divergence_local
#print axioms exists_coordinate_H2_of_weakForced
#print axioms closedL2Solution_gradient_forcing
#print axioms closedLaplacianForcing_ae
#print axioms closedL2Solution_exists_coordinate_H2

end ClosedThreeDimensional

end Yamabe3.Analysis
