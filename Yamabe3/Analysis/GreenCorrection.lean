import Yamabe3.Analysis.YamabeCoercivity
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.WeakEquation

/-!
# L2 forcing, native transposed equations, and parametrix correction

The L2 forcing below is an actual bounded linear functional on the retained
H1 completion. No Dirac functional is put in its domain. The transposed
equation is proved for the native volume, Laplacian, and scalar curvature.

The final parametrix lemma is explicitly CONDITIONAL: its point-source test
identity and L2 residual must be supplied by an actual local construction.
It does not assert existence of a local parametrix, a Green function with a
smooth representative, or positivity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory UniformSpace Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

section Transposition

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Native integration by parts remains valid for an arbitrary completed
energy element when the differentiated argument is a genuine smooth test. -/
theorem gradientEnergy_test_eq_integral (D : LeviCivitaData g) (Ω : Set M)
    (f : EnergyTest D Ω) (w : H1Zero D Ω) :
    gradientEnergy D Ω (f : H1Zero D Ω) w =
      -(∫ x, D.laplacian f x * (toL2 D Ω w) x ∂g.volumeMeasure) := by
  have hleft : ⟪f.oneSubLaplacian, toL2 D Ω w⟫_ℝ =
      (∫ x, f x * (toL2 D Ω w) x ∂g.volumeMeasure) -
        ∫ x, D.laplacian f x * (toL2 D Ω w) x ∂g.volumeMeasure := by
    rw [L2.inner_def]
    calc
      (∫ x, inner ℝ (f.oneSubLaplacian x) ((toL2 D Ω w) x) ∂g.volumeMeasure) =
          ∫ x, (f x - D.laplacian f x) * (toL2 D Ω w) x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [f.oneSubLaplacian_memLp.coeFn_toLp] with x hx
        rw [show f.oneSubLaplacian x = f x - D.laplacian f x from hx]
        simp [mul_comm]
      _ = _ := by
        have h₁ := f.memLp.integrable_mul (Lp.memLp (toL2 D Ω w))
        have h₂ := f.laplacian_memLp.integrable_mul (Lp.memLp (toL2 D Ω w))
        simpa only [Pi.mul_apply, sub_mul] using integral_sub h₁ h₂
  have hpair : ⟪testToL2 D Ω f, toL2 D Ω w⟫_ℝ =
      ∫ x, f x * (toL2 D Ω w) x ∂g.volumeMeasure := by
    rw [real_inner_comm, integral_test_mul]
  rw [gradientEnergy_apply, inner_test_eq_oneSubLaplacian, toL2_coe, hleft, hpair]
  ring

/-- The potential term transfers to the native L2 representative without
assuming a pointwise representative for the H1 energy element. -/
theorem potentialForm_test_eq_integral (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (f : EnergyTest D Ω) (w : H1Zero D Ω) :
    potentialForm D Ω hc V hV (f : H1Zero D Ω) w =
      ∫ x, V x * f x * (toL2 D Ω w) x ∂g.volumeMeasure := by
  rw [potentialForm_apply, energyMulSmooth_coe, toL2_coe, real_inner_comm,
    ← integral_test_mul]
  rfl

/-- The retained Schrödinger energy pairing with a smooth test is exactly
the distributional pairing against the native differential operator. -/
theorem schrodingerForm_test_eq_integral (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (a : ℝ) (V : M → ℝ)
    (hV : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V)
    (w : H1Zero D Ω) (f : EnergyTest D Ω) :
    schrodingerForm D Ω hc a V hV w (f : H1Zero D Ω) =
      ∫ x, (-a * D.laplacian f x + V x * f x) *
        (toL2 D Ω w) x ∂g.volumeMeasure := by
  have hΔ : Integrable (fun x => D.laplacian f x * (toL2 D Ω w) x)
      g.volumeMeasure := f.laplacian_memLp.integrable_mul (Lp.memLp (toL2 D Ω w))
  have hpot : Integrable (fun x => V x * f x * (toL2 D Ω w) x)
      g.volumeMeasure := (f.mulSmooth V hV).memLp.integrable_mul (Lp.memLp (toL2 D Ω w))
  rw [schrodingerForm_symm D Ω hc a V hV w (f : H1Zero D Ω),
    schrodingerForm_apply, gradientEnergy_test_eq_integral,
    potentialForm_test_eq_integral]
  calc
    a * -(∫ x, D.laplacian f x * (toL2 D Ω w) x ∂g.volumeMeasure) +
        (∫ x, V x * f x * (toL2 D Ω w) x ∂g.volumeMeasure) =
      ∫ x, (-a) * (D.laplacian f x * (toL2 D Ω w) x) +
        V x * f x * (toL2 D Ω w) x ∂g.volumeMeasure := by
      erw [integral_add (hΔ.const_mul (-a)) hpot, integral_const_mul]
      ring
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring

end Transposition

section ClosedThreeDimensional

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual continuous L2 forcing on the native H1 completion. -/
def closedL2Forcing (g : RiemannianMetric 3 M) (F : Lp ℝ 2 g.volumeMeasure) :
    H1Zero g.leviCivitaData univ →L[ℝ] ℝ :=
  (innerSL ℝ F).comp (toL2 g.leviCivitaData univ)

omit [CompactSpace M] [ConnectedSpace M] in
@[simp] theorem closedL2Forcing_apply (g : RiemannianMetric 3 M)
    (F : Lp ℝ 2 g.volumeMeasure) (w : H1Zero g.leviCivitaData univ) :
    closedL2Forcing g F w = ⟪F, toL2 g.leviCivitaData univ w⟫_ℝ := rfl

omit [CompactSpace M] [ConnectedSpace M] in
theorem closedL2Forcing_apply_test (g : RiemannianMetric 3 M)
    (F : Lp ℝ 2 g.volumeMeasure) (f : EnergyTest g.leviCivitaData univ) :
    closedL2Forcing g F (f : H1Zero g.leviCivitaData univ) =
      ∫ x, f x * F x ∂g.volumeMeasure := by
  rw [closedL2Forcing_apply, toL2_coe, integral_test_mul]

/-- Solve `P_g w = F` only for genuine L2 forcing. -/
def closedConformalLaplacianL2Solution (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure) :
    H1Zero g.leviCivitaData univ :=
  closedConformalLaplacianInverse g hY (closedL2Forcing g F)

theorem closedConformalLaplacianL2Solution_spec (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure)
    (w : H1Zero g.leviCivitaData univ) :
    closedConformalLaplacianForm g (closedConformalLaplacianL2Solution g hY F) w =
      closedL2Forcing g F w :=
  closedConformalLaplacianInverse_spec g hY (closedL2Forcing g F) w

omit [ConnectedSpace M] in
theorem closedYamabeForm_test_eq_integral (g : RiemannianMetric 3 M)
    (w : H1Zero g.leviCivitaData univ) (f : EnergyTest g.leviCivitaData univ) :
    closedYamabeForm g w (f : H1Zero g.leviCivitaData univ) =
      ∫ x, (-8 * g.leviCivitaData.laplacian f x +
        g.leviCivitaData.scalarCurvature x * f x) *
        (toL2 g.leviCivitaData univ w) x ∂g.volumeMeasure := by
  exact schrodingerForm_test_eq_integral _ _ _ _ _ _ _ _

omit [ConnectedSpace M] in
theorem closedConformalLaplacianForm_test_eq_integral (g : RiemannianMetric 3 M)
    (w : H1Zero g.leviCivitaData univ) (f : EnergyTest g.leviCivitaData univ) :
    closedConformalLaplacianForm g w (f : H1Zero g.leviCivitaData univ) =
      ∫ x, (-g.leviCivitaData.laplacian f x +
        (g.leviCivitaData.scalarCurvature x / 8) * f x) *
        (toL2 g.leviCivitaData univ w) x ∂g.volumeMeasure := by
  rw [closedConformalLaplacianForm_apply, closedYamabeForm_test_eq_integral,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

/-- The actual representative of the L2-forced energy solution satisfies
the native transposed equation. No regularity theorem is assumed here. -/
theorem closedConformalLaplacianL2Solution_transposed (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (F : Lp ℝ 2 g.volumeMeasure)
    (f : EnergyTest g.leviCivitaData univ) :
    (∫ x, (-g.leviCivitaData.laplacian f x +
        (g.leviCivitaData.scalarCurvature x / 8) * f x) *
        (toL2 g.leviCivitaData univ (closedConformalLaplacianL2Solution g hY F)) x
        ∂g.volumeMeasure) = ∫ x, f x * F x ∂g.volumeMeasure := by
  rw [← closedConformalLaplacianForm_test_eq_integral,
    closedConformalLaplacianL2Solution_spec, closedL2Forcing_apply_test]

omit [CompactSpace M] [ConnectedSpace M] in
/-- The differential operator applied to a genuine compact test is in L2.
This proves the integrability needed in transposed pairings with a singular
parametrix that itself belongs to L2 in dimension three. -/
theorem conformalLaplacian_test_memLp (g : RiemannianMetric 3 M)
    (f : EnergyTest g.leviCivitaData univ) :
    MemLp (fun x => -g.leviCivitaData.laplacian f x +
      (g.leviCivitaData.scalarCurvature x / 8) * f x) 2 g.volumeMeasure := by
  have hV := (f.mulSmooth g.leviCivitaData.scalarCurvature
    g.leviCivitaData.contMDiff_scalarCurvature).memLp
  convert f.laplacian_memLp.neg.add (hV.const_mul (1 / 8 : ℝ)) using 1
  ext x
  simp only [Pi.add_apply, Pi.neg_apply, EnergyTest.mulSmooth_apply]
  ring

/-- Legal residual correction for an already established native point-source
test identity. The assumption `hparam` is a real outstanding obligation, not
a supplied Green existence theorem. The conclusion is only an L2
distributional Green candidate, with no pointwise regularity or positivity
claim. -/
theorem parametrix_sub_L2Solution_test (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M)
    (Φ F : M → ℝ) (hΦ : MemLp Φ 2 g.volumeMeasure)
    (hF : MemLp F 2 g.volumeMeasure)
    (hparam : ∀ f : EnergyTest g.leviCivitaData univ,
      (∫ x, (-g.leviCivitaData.laplacian f x +
          (g.leviCivitaData.scalarCurvature x / 8) * f x) * Φ x ∂g.volumeMeasure) =
        4 * Real.pi * f p + ∫ x, f x * F x ∂g.volumeMeasure) :
    let w := closedConformalLaplacianL2Solution g hY (hF.toLp F)
    let G := fun x => Φ x - (toL2 g.leviCivitaData univ w) x
    MemLp G 2 g.volumeMeasure ∧
      ∀ f : EnergyTest g.leviCivitaData univ,
        (∫ x, (-g.leviCivitaData.laplacian f x +
            (g.leviCivitaData.scalarCurvature x / 8) * f x) * G x ∂g.volumeMeasure) =
          4 * Real.pi * f p := by
  dsimp only
  let w := closedConformalLaplacianL2Solution g hY (hF.toLp F)
  refine ⟨hΦ.sub (Lp.memLp (toL2 g.leviCivitaData univ w)), fun f => ?_⟩
  have hc := closedConformalLaplacianL2Solution_transposed g hY (hF.toLp F) f
  have hsource : (∫ x, f x * (hF.toLp F) x ∂g.volumeMeasure) =
      ∫ x, f x * F x ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with x hx
    rw [hx]
  rw [hsource] at hc
  have hleft := (conformalLaplacian_test_memLp g f).integrable_mul hΦ
  have hright := (conformalLaplacian_test_memLp g f).integrable_mul
    (Lp.memLp (toL2 g.leviCivitaData univ w))
  simp only [mul_sub]
  erw [integral_sub hleft hright, hparam f, hc]
  ring

#print axioms gradientEnergy_test_eq_integral
#print axioms potentialForm_test_eq_integral
#print axioms schrodingerForm_test_eq_integral
#print axioms closedConformalLaplacianL2Solution_transposed
#print axioms conformalLaplacian_test_memLp
#print axioms parametrix_sub_L2Solution_test

end ClosedThreeDimensional

end Yamabe3.Analysis
