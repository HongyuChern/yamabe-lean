import Yamabe3.Geometry.Completeness
import Yamabe3.Geometry.OpenRestriction
import GreenMass.PuncturedEnd
import PoincareLib.Geometry.Riemannian.Distance.TangentBound

/-!
# Actual completeness by domination of complete single-puncture metrics

A Cauchy sequence for the multiple-puncture metric has, by actual native
Lipschitz inclusion, a limit in each complete single-puncture metric. The
underlying limits agree in the Hausdorff ambient manifold, so their common
limit avoids every deleted point. This gives native metric completeness
without using any derivative asymptotics for a Green correction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

namespace Yamabe3.Geometry

open PoincareMT GreenMass.PuncturedEnd

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The actual open complement of the prescribed finite pole set. -/
def finitePuncture (Λ : Finset M) : Opens M :=
  ⟨(Λ : Set M)ᶜ, Λ.finite_toSet.isClosed.isOpen_compl⟩

/-- The actual inclusion into one of the single-puncture manifolds. -/
def finitePunctureInclusion (Λ : Finset M) (p : M) (hp : p ∈ Λ) :
    finitePuncture Λ → puncture p := fun x =>
  ⟨x.val, fun hxp => x.property (hxp.symm ▸ hp)⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] in
@[simp] theorem finitePunctureInclusion_val (Λ : Finset M) (p : M) (hp : p ∈ Λ)
    (x : finitePuncture Λ) : (finitePunctureInclusion Λ p hp x).val = x.val := rfl

omit [IsManifold (𝓡 3) ∞ M] in
theorem contMDiff_finitePunctureInclusion (Λ : Finset M) (p : M) (hp : p ∈ Λ) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (finitePunctureInclusion Λ p hp) := by
  intro x
  apply (ContMDiffAt.subtypeVal_comp_iff (puncture p)
    (finitePunctureInclusion Λ p hp) x).mp
  exact contMDiff_subtype_val (I := 𝓡 3) (U := finitePuncture Λ) (n := ∞) x

/-- Pulling the single-puncture restriction through the actual inclusion
recovers exactly the same ambient tangent norm. -/
theorem tangentNorm_finitePunctureInclusion (g : RiemannianMetric 3 M)
    (Λ : Finset M) (p : M) (hp : p ∈ Λ) (x : finitePuncture Λ)
    (v : TangentSpace (𝓡 3) x) :
    (restrictMetric g (puncture p)).tangentNorm (finitePunctureInclusion Λ p hp x)
      (mfderiv (𝓡 3) (𝓡 3) (finitePunctureInclusion Λ p hp) x v) =
        (restrictMetric g (finitePuncture Λ)).tangentNorm x v := by
  let j := finitePunctureInclusion Λ p hp
  have hj := contMDiff_finitePunctureInclusion Λ p hp
  have hval := contMDiff_subtype_val (I := 𝓡 3) (U := puncture p) (n := ∞)
  have hchain := mfderiv_comp x ((hval (j x)).mdifferentiableAt (by simp))
    ((hj x).mdifferentiableAt (by simp))
  have heq : (Subtype.val : puncture p → M) ∘ j =
      (Subtype.val : finitePuncture Λ → M) := rfl
  rw [heq] at hchain
  have hvec := congrArg (fun A => A v) hchain
  change Real.sqrt (g.inner x.val
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : puncture p → M) (j x)
      (mfderiv (𝓡 3) (𝓡 3) j x v))
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : puncture p → M) (j x)
      (mfderiv (𝓡 3) (𝓡 3) j x v))) =
    Real.sqrt (g.inner x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : finitePuncture Λ → M) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : finitePuncture Λ → M) x v))
  exact congrArg (fun w => Real.sqrt (g.inner x.val w w)) hvec.symm

/-- If H dominates a positive multiple of one Green factor, its actual
conformal distance dominates the corresponding single-puncture distance.
The comparison follows from the actual inclusion differential and actual
fourth-power conformal tangent norms. -/
theorem singlePuncture_conformal_edist_le (g : RiemannianMetric 3 M)
    (Λ : Finset M) (p : M) (hp : p ∈ Λ) (H G : M → ℝ)
    (hH : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : finitePuncture Λ => H x.val))
    (hG : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : puncture p => G x.val))
    (hHpos : ∀ x : finitePuncture Λ, 0 < H x.val)
    (hGpos : ∀ x : puncture p, 0 < G x.val)
    {a : ℝ} (ha : 0 < a) (hdom : ∀ x : finitePuncture Λ, a * G x.val ≤ H x.val)
    (x y : finitePuncture Λ) :
    (MetricSurgery.positiveScaling (restrictMetric g (puncture p))
      (fun z => G z.val ^ 4) (hG.pow 4) (fun z => pow_pos (hGpos z) 4)).edist
        (finitePunctureInclusion Λ p hp x) (finitePunctureInclusion Λ p hp y) ≤
      ENNReal.ofReal ((a⁻¹) ^ 2) *
        (MetricSurgery.positiveScaling (restrictMetric g (finitePuncture Λ))
          (fun z => H z.val ^ 4) (hH.pow 4) (fun z => pow_pos (hHpos z) 4)).edist x y := by
  apply RiemannianMetric.edist_le_mul_of_tangentNorm_mfderiv_le _ _
    ((contMDiff_finitePunctureInclusion Λ p hp).of_le (by simp)) (sq_pos_of_pos (inv_pos.mpr ha))
  intro z v
  rw [tangentNorm_positiveScaling_fourth (restrictMetric g (puncture p))
      (fun x => G x.val) hG hGpos,
    tangentNorm_positiveScaling_fourth (restrictMetric g (finitePuncture Λ))
      (fun x => H x.val) hH hHpos,
    tangentNorm_finitePunctureInclusion]
  have hlin : G z.val ≤ H z.val / a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hdom z)
  have hsq : G z.val ^ 2 ≤ (H z.val / a) ^ 2 :=
    (sq_le_sq₀ (hGpos (finitePunctureInclusion Λ p hp z)).le
      (div_pos (hHpos z) ha).le).mpr hlin
  have hsq' : G z.val ^ 2 ≤ (a⁻¹) ^ 2 * H z.val ^ 2 := by
    simpa only [div_eq_mul_inv, mul_pow, inv_pow, mul_comm] using hsq
  calc
    _ ≤ ((a⁻¹) ^ 2 * H z.val ^ 2) *
        (restrictMetric g (finitePuncture Λ)).tangentNorm z v :=
      mul_le_mul_of_nonneg_right hsq' (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Native completeness transfers from the complete one-puncture metrics
when every actual inclusion satisfies its proved finite distance bound.
The Hausdorff ambient space identifies the limits and excludes all poles. -/
theorem metricComplete_of_singlePuncture_comparisons
    (Λ : Finset M) (hΛ : Λ.Nonempty)
    (gH : RiemannianMetric 3 (finitePuncture Λ))
    (gP : ∀ p ∈ Λ, RiemannianMetric 3 (puncture p))
    (hPcomplete : ∀ p hp, MetricComplete (gP p hp))
    (hcompare : ∀ p hp, ∃ C : ℝ, 0 < C ∧
      ∀ x y : finitePuncture Λ,
        (gP p hp).edist (finitePunctureInclusion Λ p hp x)
          (finitePunctureInclusion Λ p hp y) ≤ ENNReal.ofReal C * gH.edist x y) :
    MetricComplete gH := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : finitePuncture Λ → Type _) :=
    ⟨gH.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : finitePuncture Λ → Type _) :=
    ⟨⟨gH.inner, gH.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (finitePuncture Λ) :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) (finitePuncture Λ)
  change CompleteSpace (finitePuncture Λ)
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hlimits (p : M) (hp : p ∈ Λ) :
      ∃ y : M, y ≠ p ∧ Tendsto (fun k => (u k).val) atTop (𝓝 y) := by
    let g := gP p hp
    let j := finitePunctureInclusion Λ p hp
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : puncture p → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : puncture p → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace (puncture p) := EMetricSpace.ofRiemannianMetric (𝓡 3) (puncture p)
    let : CompleteSpace (puncture p) := hPcomplete p hp
    obtain ⟨C, hC, hbound⟩ := hcompare p hp
    have hj : LipschitzWith ⟨C, hC.le⟩ j := by
      intro x y
      change g.edist (j x) (j y) ≤ ENNReal.ofNNReal ⟨C, hC.le⟩ * gH.edist x y
      simpa only [g, j, ENNReal.ofReal_eq_coe_nnreal hC.le, NNReal.mk] using hbound x y
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hj.uniformContinuous.comp_cauchySeq hu)
    refine ⟨y.val, y.property, ?_⟩
    simpa only [Function.comp_def, j, finitePunctureInclusion_val] using
      (continuous_subtype_val.continuousAt.tendsto.comp hy)
  obtain ⟨p, hp⟩ := hΛ
  obtain ⟨y, _, hy⟩ := hlimits p hp
  have hyΛ : y ∉ Λ := by
    intro hyMem
    obtain ⟨z, hzy, hz⟩ := hlimits y hyMem
    exact hzy (tendsto_nhds_unique hz hy)
  exact ⟨⟨y, hyΛ⟩, tendsto_subtype_rng.mpr hy⟩

#print axioms tangentNorm_finitePunctureInclusion
#print axioms singlePuncture_conformal_edist_le
#print axioms metricComplete_of_singlePuncture_comparisons

end Yamabe3.Geometry
