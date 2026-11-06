import Yamabe3.Analysis.NativeWeakPhysicalConormal

/-!
# Genuine H1 gluing from equality of physical value traces

The exterior restriction of the zero-trace difference is constructed by
its proved cutoff limit. A single global H1 element has the literal piecewise
volume representative and the exact split gradient energy. Matching the
physical conormal remains a separate equation, not a conclusion of value matching.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option quotPrecheck false
open Set Filter MeasureTheory UniformSpace PoincareMT Metric
open scoped Manifold ContDiff InnerProductSpace Topology
namespace Yamabe3.Analysis
open PoincareMT.LeviCivitaData.Dirichlet SpherePolar NativeChartSphereMetric
variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

theorem nativeRestrictedGradientEnergy_add_compl (g : RiemannianMetric 3 M)
    (Ω : Set M) (hΩ : MeasurableSet Ω)
    (v w : H1Zero g.leviCivitaData univ) :
    nativeRestrictedGradientEnergy g Ω v w + nativeRestrictedGradientEnergy g Ωᶜ v w =
      gradientEnergy g.leviCivitaData univ v w := by
  induction v using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v =>
    induction w using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih w =>
      rw [nativeRestrictedGradientEnergy_coe, nativeRestrictedGradientEnergy_coe,
        gradientEnergy_coe]
      exact integral_add_compl hΩ (v.integrable_gradient w)

theorem nativeGlobalPotentialForm_integral (g : RiemannianMetric 3 M)
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (v w : H1Zero g.leviCivitaData univ) :
    potentialForm g.leviCivitaData univ (by simpa using isCompact_univ) V hV v w =
      ∫ x, V x * toL2 g.leviCivitaData univ v x * toL2 g.leviCivitaData univ w x
        ∂g.volumeMeasure := by
  have hi : nativeDomainEnergyInclusion g univ w = w := by
    induction w using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih w => rw [nativeDomainEnergyInclusion_coe]; rfl
  have h := nativeRestrictedPotentialForm_domain_right g univ V hV v w
  rw [hi] at h
  rw [← h, nativeRestrictedPotentialForm_integral, Measure.restrict_univ]


variable (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E)
  (e : OpenPartialHomeomorph E M)
  (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
  (hGauss : ∀ x v : E, gE.inner x x v = inner ℝ x v)
  {a C : ℝ} (ha : 0 < a)
  (hs : closedBall (0 : E) (2 * a) ⊆ e.source)
  (hcoeff : ∀ x ∈ closedBall (0 : E) (2 * a),
    gE.euclideanCoefficients x = g.pullbackCoefficients e x)
  (hC : 0 ≤ C)
  (hρ : ∀ θ : S, gE.pullbackVolumeDensity id (a • (θ : E)) ≤ C)

include hs in
private theorem weakGluing_annulus_source : sphereTraceAnnulus a (2 * a) ⊆ e.source := by
  intro x hx
  exact hs (by simpa only [mem_closedBall, dist_zero_right] using hx.2)
local notation "T" => nativePhysicalSphereTraceCLM g gE e he hei ha
  (show a < 2 * a from by linarith only [ha])
  (show a ∈ Icc a (2 * a) from ⟨le_rfl, by linarith only [ha]⟩)
  (weakGluing_annulus_source e hs) hC
  (fun θ => hcoeff _ (by
    rw [mem_closedBall, dist_zero_right, EuclideanSphereTrace.norm_sphereTrace_radial _ ha.le]
    linarith only [ha]))
  (fun θ => hGauss (a • (θ : E))) hρ
local notation "Oext" => (e '' closedBall (0 : E) a)ᶜ
attribute [local instance] Classical.propDecidable

/-- Equal actual physical traces produce a single H1 realization of the
piecewise function; the same element works for every completed test. -/
theorem exists_native_physical_H1_gluing
    (win wout : H1Zero g.leviCivitaData univ) (hT : T wout = T win) :
    ∃ W : H1Zero g.leviCivitaData univ,
      (toL2 g.leviCivitaData univ W : M → ℝ) =ᵐ[g.volumeMeasure]
        (Oext).piecewise (toL2 g.leviCivitaData univ wout) (toL2 g.leviCivitaData univ win) ∧
      ∀ η : H1Zero g.leviCivitaData univ,
        gradientEnergy g.leviCivitaData univ W η =
          nativeRestrictedGradientEnergy g Oext wout η +
            nativeRestrictedGradientEnergy g (Oext)ᶜ win η := by
  have hzero : T (wout - win) = 0 := by
    exact (map_sub T wout win).trans (sub_eq_zero.mpr hT)
  obtain ⟨q, hq, _, hgrad⟩ := EuclideanSphereTrace.exists_native_zero_trace_exterior_restriction
    g gE e he hei hGauss ha hs hcoeff hC hρ (wout - win) hzero
  let Iq := nativeDomainEnergyInclusion g Oext q
  let W := win + Iq
  have hΩ : MeasurableSet Oext :=
    ((isCompact_closedBall (0 : E) a).image_of_continuousOn
      (e.continuousOn.mono ((closedBall_subset_closedBall (by linarith only [ha])).trans hs))).measurableSet.compl
  have hsub : (toL2 g.leviCivitaData univ (wout - win) : M → ℝ) =ᵐ[g.volumeMeasure]
      fun x => toL2 g.leviCivitaData univ wout x - toL2 g.leviCivitaData univ win x := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  have hadd : (toL2 g.leviCivitaData univ W : M → ℝ) =ᵐ[g.volumeMeasure]
      fun x => toL2 g.leviCivitaData univ win x + toL2 g.leviCivitaData Oext q x := by
    dsimp only [W, Iq]
    rw [map_add, nativeDomainEnergyInclusion_toL2]
    exact Lp.coeFn_add _ _
  refine ⟨W, ?_, ?_⟩
  · filter_upwards [hadd, hq, hsub] with x hx hy hz
    rw [hx, hy]
    by_cases hm : x ∈ Oext
    · simp only [indicator_of_mem hm, piecewise_eq_of_mem _ _ _ hm]
      rw [hz]
      ring
    · simp only [indicator_of_notMem hm, piecewise_eq_of_notMem _ _ _ hm, add_zero]
  · intro η
    have hg : gradientEnergy g.leviCivitaData univ Iq η =
        nativeRestrictedGradientEnergy g Oext (wout - win) η := by
      rw [gradientEnergy_symm]
      exact (hgrad η).symm.trans (nativeRestrictedGradientEnergy_symm g Oext η (wout - win))
    change gradientEnergy g.leviCivitaData univ (win + Iq) η = _
    rw [map_add, ContinuousLinearMap.add_apply, hg,
      map_sub, ContinuousLinearMap.sub_apply]
    have hc := nativeRestrictedGradientEnergy_add_compl g Oext hΩ win η
    linarith only [hc]

/-- The same glued H1 element also has the exact native elliptic energy
split. This adds the potential pairing without assigning boundary values to
an L2 representative and without assuming a weak equation. -/
theorem exists_native_physical_energy_gluing
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (win wout : H1Zero g.leviCivitaData univ) (hT : T wout = T win) :
    ∃ W : H1Zero g.leviCivitaData univ,
      (toL2 g.leviCivitaData univ W : M → ℝ) =ᵐ[g.volumeMeasure]
        (Oext).piecewise (toL2 g.leviCivitaData univ wout) (toL2 g.leviCivitaData univ win) ∧
      ∀ η : H1Zero g.leviCivitaData univ,
        schrodingerForm g.leviCivitaData univ (by simpa using isCompact_univ) 8 V hV W η =
          nativeRestrictedEllipticForm g Oext V hV wout η +
            nativeRestrictedEllipticForm g (Oext)ᶜ V hV win η := by
  obtain ⟨W, hrep, hgrad⟩ := exists_native_physical_H1_gluing g gE e he hei hGauss ha hs
    hcoeff hC hρ win wout hT
  have hΩ : MeasurableSet Oext :=
    ((isCompact_closedBall (0 : E) a).image_of_continuousOn
      (e.continuousOn.mono ((closedBall_subset_closedBall (by linarith only [ha])).trans hs))).measurableSet.compl
  refine ⟨W, hrep, fun η => ?_⟩
  have hp : potentialForm g.leviCivitaData univ (by simpa using isCompact_univ) V hV W η =
      nativeRestrictedPotentialForm g Oext V hV wout η +
        nativeRestrictedPotentialForm g (Oext)ᶜ V hV win η := by
    rw [nativeGlobalPotentialForm_integral, nativeRestrictedPotentialForm_integral,
      nativeRestrictedPotentialForm_integral]
    calc
      _ = ∫ x, (Oext).piecewise
          (fun x => V x * toL2 g.leviCivitaData univ wout x * toL2 g.leviCivitaData univ η x)
          (fun x => V x * toL2 g.leviCivitaData univ win x * toL2 g.leviCivitaData univ η x) x
            ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [hrep] with x hx
        rw [hx]
        by_cases hm : x ∈ Oext <;> simp only [piecewise, hm, ite_true, ite_false]
      _ = _ := integral_piecewise hΩ
        (nativeRestrictedPotentialForm_integrable g Oext V hV wout η)
        (nativeRestrictedPotentialForm_integrable g (Oext)ᶜ V hV win η)
  rw [schrodingerForm_apply, hgrad η, hp,
    nativeRestrictedEllipticForm_apply, nativeRestrictedEllipticForm_apply]
  ring

/-- Exact interface residual for the same glued element and the same native
source. This is an equivalence/consumer: no cancellation is assumed to hold,
and no conormal matching producer is asserted. -/
theorem exists_native_physical_gluing_residual
    (V : M → ℝ) (hV : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ V)
    (win wout : H1Zero g.leviCivitaData univ) (hT : T wout = T win)
    (F : Lp ℝ 2 g.volumeMeasure) :
    ∃ W : H1Zero g.leviCivitaData univ,
      (toL2 g.leviCivitaData univ W : M → ℝ) =ᵐ[g.volumeMeasure]
        (Oext).piecewise (toL2 g.leviCivitaData univ wout) (toL2 g.leviCivitaData univ win) ∧
      (∀ η : H1Zero g.leviCivitaData univ,
        schrodingerForm g.leviCivitaData univ (by simpa using isCompact_univ) 8 V hV W η -
          (∫ x, F x * toL2 g.leviCivitaData univ η x ∂g.volumeMeasure) =
          nativeWeakEnergySourceDataCLM g Oext V hV (wout, F) η +
          nativeWeakEnergySourceDataCLM g (Oext)ᶜ V hV (win, F) η) ∧
      ((∀ η : H1Zero g.leviCivitaData univ,
        schrodingerForm g.leviCivitaData univ (by simpa using isCompact_univ) 8 V hV W η =
          ∫ x, F x * toL2 g.leviCivitaData univ η x ∂g.volumeMeasure) ↔
        ∀ η : H1Zero g.leviCivitaData univ,
          nativeWeakEnergySourceDataCLM g Oext V hV (wout, F) η +
          nativeWeakEnergySourceDataCLM g (Oext)ᶜ V hV (win, F) η = 0) := by
  obtain ⟨W, hrep, henergy⟩ := exists_native_physical_energy_gluing g gE e he hei
    hGauss ha hs hcoeff hC hρ V hV win wout hT
  have hΩ : MeasurableSet Oext :=
    ((isCompact_closedBall (0 : E) a).image_of_continuousOn
      (e.continuousOn.mono ((closedBall_subset_closedBall (by linarith only [ha])).trans hs))).measurableSet.compl
  have hres : ∀ η : H1Zero g.leviCivitaData univ,
      schrodingerForm g.leviCivitaData univ (by simpa using isCompact_univ) 8 V hV W η -
        (∫ x, F x * toL2 g.leviCivitaData univ η x ∂g.volumeMeasure) =
        nativeWeakEnergySourceDataCLM g Oext V hV (wout, F) η +
        nativeWeakEnergySourceDataCLM g (Oext)ᶜ V hV (win, F) η := by
    intro η
    have hint : Integrable (fun x => F x * toL2 g.leviCivitaData univ η x) g.volumeMeasure := by
      simpa only [IntegrableOn, Measure.restrict_univ] using
        nativeRestrictedL2SourceOperator_integrable g univ F η
    have hsplit := integral_add_compl hΩ hint
    rw [henergy η, nativeWeakEnergySourceDataCLM_apply,
      nativeWeakEnergySourceDataCLM_apply, nativeRestrictedL2SourceOperator_apply,
      nativeRestrictedL2SourceOperator_apply]
    dsimp only [Prod.fst, Prod.snd]
    linarith only [hsplit]
  refine ⟨W, hrep, hres, ?_⟩
  constructor
  · intro h η
    rw [← hres η, h η, sub_self]
  · intro h η
    exact sub_eq_zero.mp ((hres η).trans (h η))

end Yamabe3.Analysis
