import Yamabe3.Analysis.GreenNonnegativeEnergy
import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation

/-!
# Native Green nonnegativity from an actual point-source equation

The totalized value of the singular function at the pole is never used as
an asymptotic value. An actual native bump, equal to one near the pole,
removes that value before smooth positive-part testing. The near-pole sign,
true point-source identity and positive Yamabe gap then imply nonnegativity
at every point away from the pole.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace Yamabe3.Analysis.GreenPositivity

open PoincareMT
open PoincareMT.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M]

/-- A smooth off-pole native point source which is nonnegative in an actual
punctured neighborhood of its pole is nonnegative everywhere off that pole.
Only the genuine positive Yamabe condition supplies the global energy gap. -/
theorem nonneg_of_native_pointSource (g : RiemannianMetric 3 M)
    (hY : 0 < Target.yamabeConstant g) (p : M) (G : M → ℝ)
    (hGs : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ G ({p}ᶜ))
    (hnear : ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ ∀ x ∈ O, x ≠ p → 0 ≤ G x)
    (hsource : ∀ f : EnergyTest g.leviCivitaData univ,
      (∫ x, (-g.leviCivitaData.laplacian f x +
        (g.leviCivitaData.scalarCurvature x / 8) * f x) * G x ∂g.volumeMeasure) =
        4 * Real.pi * f p) :
    ∀ x : M, x ≠ p → 0 ≤ G x := by
  classical
  let D := g.leviCivitaData
  obtain ⟨O, hO, hpO, hGO⟩ := hnear
  obtain ⟨b, -, hbO⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 3) p).mem_iff.mp
    (hO.mem_nhds hpO)
  let Sfun : M → ℝ := fun x => -(1 - b x) * G x
  have hSs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ Sfun := by
    intro x
    by_cases hx : x = p
    · subst x
      have heq : Sfun =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
        filter_upwards [b.eventuallyEq_one] with y hy
        change -(1 - b y) * G y = 0
        rw [show b y = 1 from hy]
        ring
      exact contMDiffAt_const.congr_of_eventuallyEq heq
    · have hxΩ : x ∈ ({p}ᶜ : Set M) := by simpa using hx
      exact ((contMDiffAt_const.sub (b.contMDiff x)).neg).mul
        (hGs.contMDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hxΩ))
  let S : EnergyTest D univ :=
    ⟨Sfun, hSs, HasCompactSupport.of_compactSpace _, subset_univ _⟩
  have hSO (x : M) (hx : x ∈ O) : S x ≤ 0 := by
    by_cases hxp : x = p
    · subst x
      change -(1 - b p) * G p ≤ 0
      rw [b.eq_one]
      norm_num
    · exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sub_nonneg.mpr b.le_one)) (hGO x hx hxp)
  have hSout (x : M) (hx : x ∉ O) : S x = -G x := by
    have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hbO ht))
    change -(1 - b x) * G x = -G x
    simp only [hb0, sub_zero, neg_one_mul]
  have hpair (δ : ℝ) (hδ : 0 < δ) :
      closedConformalLaplacianForm g (S : H1Zero D univ)
        (positiveApproxTest g S δ : H1Zero D univ) = 0 := by
    let T := positiveApproxTest g S δ
    have hTzero (x : M) (hx : x ∈ O) : T x = 0 :=
      smoothPositiveApprox_eq_zero_of_nonpos hδ (hSO x hx)
    have hTnot (x : M) (hx : x ∈ O) : x ∉ tsupport (T : M → ℝ) := by
      apply notMem_tsupport_iff_eventuallyEq.mpr
      filter_upwards [hO.mem_nhds hx] with y hy
      exact hTzero y hy
    have htest (x : M) :
        (-D.laplacian T x + (D.scalarCurvature x / 8) * T x) * S x =
          -((-D.laplacian T x + (D.scalarCurvature x / 8) * T x) * G x) := by
      by_cases hx : x ∈ O
      · have hΔ : D.laplacian T x = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hTnot x hx (D.tsupport_laplacian_subset T ht))
        rw [hΔ, hTzero x hx]
        ring
      · rw [hSout x hx]
        ring
    calc
      _ = ∫ x, (-D.laplacian T x + (D.scalarCurvature x / 8) * T x) *
          toL2 D univ (S : H1Zero D univ) x ∂g.volumeMeasure :=
        closedConformalLaplacianForm_test_eq_integral g (S : H1Zero D univ) T
      _ = ∫ x, (-D.laplacian T x + (D.scalarCurvature x / 8) * T x) * S x
          ∂g.volumeMeasure := by
        rw [toL2_coe]
        apply integral_congr_ae
        filter_upwards [S.memLp.coeFn_toLp] with x hx
        rw [show testToL2 D univ S x = S x from hx]
      _ = -(∫ x, (-D.laplacian T x + (D.scalarCurvature x / 8) * T x) * G x
          ∂g.volumeMeasure) := by
        rw [← integral_neg]
        exact integral_congr_ae (Eventually.of_forall htest)
      _ = 0 := by rw [hsource T, hTzero p hpO]; ring
  have hSnonpos := nonpos_of_positiveApprox_pairing_zero g hY S hpair
  intro x hxp
  by_cases hx : x ∈ O
  · exact hGO x hx hxp
  · have hs := hSnonpos x
    rw [hSout x hx] at hs
    exact neg_nonpos.mp hs

#print axioms nonneg_of_native_pointSource

end Yamabe3.Analysis.GreenPositivity
