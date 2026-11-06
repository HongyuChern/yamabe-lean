import Yamabe3.Analysis.BoundaryH4WithPotential
import Yamabe3.Analysis.SobolevEuclideanChart
import Yamabe3.Analysis.BoundaryChartH4

/-! The actual retained equation, physical H2 source and smooth potential
produce H4 in a genuine boundary chart of the same completion element.
The normalized source is F/8 + Q*u; it is not assumed to have H2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff ENNReal Topology Manifold InnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Euclidean
open PoincareMT.LeviCivitaData.Dirichlet PoincareMT.LeviCivitaData.Dirichlet.Boundary
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
variable {D : LeviCivitaData (RiemannianMetric.euclideanMetric d)}

theorem exists_chart_H4_with_physical_source_bound {Ω : Set E}
    (e : OpenPartialHomeomorph E E)
    (he : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 d) (𝓡 d) ∞ e.symm e.target)
    (χ : E → ℝ) (hχ : ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0)
    (Q : E → ℝ) (hQ : ContDiffOn ℝ ∞ Q e.target)
    {W V P : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWs : closure W ⊆ e.source) (hone : ∀ z ∈ W, χ (e z) = 1)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    (hP : IsOpen P) (heP : e '' closure W ⊆ P) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (z : H1Zero D Ω) (F : E → ℝ) (G : Lp ℝ 2 (RiemannianMetric.euclideanMetric d).volumeMeasure),
      MemWkp 2 2 F P →
      ((G : E → ℝ) =ᵐ[(RiemannianMetric.euclideanMetric d).volumeMeasure]
        Ω.indicator (fun y => F y / 8 + Q y * (toL2 D Ω z : E → ℝ) y)) →
      (∀ v : H1Zero D Ω, ⟪z, v⟫_ℝ - ⟪toL2 D Ω z, toL2 D Ω v⟫_ℝ = ⟪G, toL2 D Ω v⟫_ℝ) →
      MemWkp 4 2 (chartPullback e (fun y => χ y * toL2 D Ω z y)) (V ∩ {x : E | 0 < x 0}) ∧
      iteratedWeakSobolevNorm 4 2 (chartPullback e (fun y => χ y * toL2 D Ω z y))
        (V ∩ {x : E | 0 < x 0}) ≤ K *
        (iteratedWeakSobolevNorm 1 2 (chartPullback e (fun y => χ y * toL2 D Ω z y))
          {x : E | 0 < x 0} + iteratedWeakSobolevNorm 2 2 F P) := by
  classical
  let H : Set E := {x | 0 < x 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  have hWH : IsOpen (W ∩ H) := hW.inter hH
  have hD : e.MDifferentiable (𝓡 d) (𝓡 d) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContDiffOn ℝ ∞ ((RiemannianMetric.euclideanMetric d).pullbackVolumeDensity e) e.source := by
    intro x hx
    exact ((RiemannianMetric.euclideanMetric d).contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).1.contDiffWithinAt
  have hQc : ContDiffOn ℝ ∞ (fun x => Q (e x)) e.source :=
    hQ.comp he.contDiffOn e.mapsTo
  obtain ⟨b, hb, -, hbe⟩ := exists_smooth_map_eq_on_compact e.open_source hWc hWs
    (fun x => (RiemannianMetric.euclideanMetric d).pullbackVolumeDensity e x * Q (e x)) (hρ.mul hQc)
  obtain ⟨B, hBA, -⟩ := exists_elliptic_form_on_compact (g := (RiemannianMetric.euclideanMetric d)) e he hei hWc hWs
  obtain ⟨Cp, hCp, hp⟩ := exists_euclidean_chart_density_source_bound 2 e he hei hW hWc hWs hP heP
  obtain ⟨K, hK, hreg⟩ := exists_flat_H4_with_potential_bound B b hb hW hWc hV hVc hVW
  refine ⟨K*(1+Cp/8), by finiteness, ?_⟩
  intro z F G hF hG hsol
  let u := chartPullback e (fun y => χ y * toL2 D Ω z y)
  let f : E → ℝ := fun x => (1/8 : ℝ) * ((RiemannianMetric.euclideanMetric d).pullbackVolumeDensity e x * F (e x))
  have hfW := MemWkp.const_smul (by norm_num : (1 : ℝ≥0∞) ≤ 2) hW (hp F hF).1 (1/8)
  have hf : MemWkp 2 2 f (W ∩ H) := hfW.mono_set (by norm_num) hWH inter_subset_left
  have hfn : iteratedWeakSobolevNorm 2 2 f (W ∩ H) ≤ (Cp/8) * iteratedWeakSobolevNorm 2 2 F P := by
    calc
      _ ≤ iteratedWeakSobolevNorm 2 2 f W := wkpNorm_mono_set (by norm_num) hWH inter_subset_left hfW
      _ = (1/8 : ℝ≥0∞) * iteratedWeakSobolevNorm 2 2
          (fun x => (RiemannianMetric.euclideanMetric d).pullbackVolumeDensity e x * F (e x)) W := by
        rw [wkpNorm_const_smul (by norm_num) hW (hp F hF).1]
        rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 1/8)]
        simp only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      _ ≤ (1/8 : ℝ≥0∞) * (Cp * iteratedWeakSobolevNorm 2 2 F P) :=
        mul_le_mul le_rfl (hp F hF).2 zero_le zero_le
      _ = _ := by simp only [div_eq_mul_inv, one_mul]; ring
  obtain ⟨hu0, p, hpLp, hw, -, -, heq⟩ := weakSolution_localized_divergence
    e he hei χ hχ hc hs hflat hW hWc hWs hone z G hsol
  have hchosen (j : Fin d) : chosenWeakPartial' 2 j u H =ᵐ[volume.restrict H] p j :=
    Weak.HasWeakPartialDeriv.ae_eq hH
      (chosenWeakPartial'_isWeakPartial_of_mem hu0.1 j) (hw j)
      ((chosenWeakPartial'_memLp_of_mem hu0.1 j).locallyIntegrable (by norm_num))
      ((hpLp j).locallyIntegrable (by norm_num))
  have hGp : (fun x => G (e x)) =ᵐ[volume.restrict (W ∩ H)]
      (fun x => Ω.indicator (fun y => F y / 8 + Q y * (toL2 D Ω z : E → ℝ) y) (e x)) :=
    ((RiemannianMetric.euclideanMetric d).ae_comp_on_compact e he hei hWc hWs hG).filter_mono
    (ae_mono (Measure.restrict_mono_set volume (inter_subset_left.trans subset_closure)))
  have hactual : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W ∩ H →
      (∫ x in W ∩ H, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u H x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in W ∩ H, (f x + b x * u x) * φ x := by
    intro φ hφ hφc hφs
    refine Eq.trans ?_ ((heq φ hφ hφc hφs).trans ?_)
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem hWH.measurableSet,
        (eventually_all.mpr hchosen).filter_mono (ae_mono (Measure.restrict_mono_set volume inter_subset_right))]
        with x hx hpx
      simp only [hBA (subset_closure hx.1), hpx]
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem hWH.measurableSet, hGp] with x hx hGx
      have hxs := hWs (subset_closure hx.1)
      have hxΩ := (hflat x hxs).mpr hx.2
      have hux : u x = toL2 D Ω z (e x) := by
        simp only [u, chartPullback_apply e _ hxs, hone x hx.1, one_mul]
      rw [hGx, indicator_of_mem hxΩ, hbe (subset_closure hx.1), hux]
      dsimp only [f]
      ring
  obtain ⟨hu4, hu4n⟩ := hreg u f hu0 hf hactual
  refine ⟨hu4, ?_⟩
  let N := iteratedWeakSobolevNorm 1 2 u H + iteratedWeakSobolevNorm 2 2 F P
  calc
    _ ≤ _ := hu4n
    _ ≤ K*(N+(Cp/8)*N) := mul_le_mul le_rfl
      (add_le_add (le_add_right le_rfl)
        (hfn.trans (mul_le_mul le_rfl (le_add_left le_rfl) zero_le zero_le))) zero_le zero_le
    _ = _ := by ring

#print axioms exists_chart_H4_with_physical_source_bound
end Yamabe3.Analysis.UniformElliptic
