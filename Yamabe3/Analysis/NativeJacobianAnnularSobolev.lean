import Yamabe3.Analysis.NativeJacobianChartEquation
import Yamabe3.Analysis.UniformElliptic.NativeJacobianPotentialJets
import Yamabe3.Analysis.UniformElliptic.NativeScaledCoefficients
import Yamabe3.Analysis.UniformElliptic.LocalUniformSobolev

/-!
# Uniform annular gain of two derivatives for the actual native Jacobian

One fixed normal metric extension supplies the actual rescaled principal
coefficients. Its density and scalar curvature, and the actual background's
finite jets, supply the signed potential. The same native solution then
satisfies the proved rescaled weak equation and the local Sobolev estimate.
The constant is chosen before the radius, background, solution and forcing.

For k=2 the source profile has order two and the solution profile order four.
The background-jet premise is a concrete obligation for the literal cutoff
family, treated by NativeExteriorCutoffLocalJets; it is not an assumption of
the final existence target. No C0 estimate is used to absorb second derivatives.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Yamabe3.Analysis.NativeJacobianAnnulus

open PoincareMT UniformElliptic GreenParametrix
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def outerAnnulus : Set E3 := {z | (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 2}
def sourceAnnulus : Set E3 := {z | (3 / 4 : ℝ) < ‖z‖ ∧ ‖z‖ < 3 / 2}
def innerAnnulus : Set E3 := {z | (7 / 8 : ℝ) < ‖z‖ ∧ ‖z‖ < 9 / 8}

private theorem open_norm_annulus (a b : ℝ) :
    IsOpen {z : E3 | a < ‖z‖ ∧ ‖z‖ < b} :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem outerAnnulus_open : IsOpen outerAnnulus := open_norm_annulus _ _
theorem sourceAnnulus_open : IsOpen sourceAnnulus := open_norm_annulus _ _
theorem innerAnnulus_open : IsOpen innerAnnulus := open_norm_annulus _ _

private theorem norm_bounds_of_mem_closure_annulus {a b : ℝ} {z : E3}
    (hz : z ∈ closure {z : E3 | a < ‖z‖ ∧ ‖z‖ < b}) :
    a ≤ ‖z‖ ∧ ‖z‖ ≤ b :=
  closure_minimal (show {x : E3 | a < ‖x‖ ∧ ‖x‖ < b} ⊆
      {x : E3 | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} from fun _ h => ⟨h.1.le, h.2.le⟩)
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)) hz

private theorem precompact_norm_annulus (a b : ℝ) :
    IsCompact (closure {z : E3 | a < ‖z‖ ∧ ‖z‖ < b}) := by
  apply (isCompact_closedBall (0 : E3) b).of_isClosed_subset isClosed_closure
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using
    (norm_bounds_of_mem_closure_annulus hz).2

theorem sourceAnnulus_precompact : IsCompact (closure sourceAnnulus) :=
  precompact_norm_annulus _ _

theorem innerAnnulus_precompact : IsCompact (closure innerAnnulus) :=
  precompact_norm_annulus _ _

theorem closure_sourceAnnulus_subset_outer : closure sourceAnnulus ⊆ outerAnnulus := by
  intro z hz
  have h := norm_bounds_of_mem_closure_annulus hz
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem closure_innerAnnulus_subset_source : closure innerAnnulus ⊆ sourceAnnulus := by
  intro z hz
  have h := norm_bounds_of_mem_closure_annulus hz
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem closure_sourceAnnulus_subset_ball : closure sourceAnnulus ⊆ ball (0 : E3) 3 := by
  intro z hz
  have h := (norm_bounds_of_mem_closure_annulus hz).2
  rw [mem_ball, dist_zero_right]
  linarith

theorem unitSphere_subset_innerAnnulus : sphere (0 : E3) 1 ⊆ innerAnnulus := by
  intro z hz
  have hn : ‖z‖ = 1 := by simpa using hz
  change (7 / 8 : ℝ) < ‖z‖ ∧ ‖z‖ < 9 / 8
  rw [hn]
  norm_num

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]

/-- A uniform local derivative estimate for the same actual native solution
and native Jacobian. Ellipticity, matrix jets and the signed-potential bound
are proved from the fixed metric and the actual background jets. -/
theorem exists_uniform_native_chart_jacobian_annular_bound
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 E3)
    (e : OpenPartialHomeomorph E3 M)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {R : ℝ} (hR : 0 < R) (hsource : closedBall (0 : E3) R ⊆ e.source)
    (hcoeff : ∀ x ∈ closedBall (0 : E3) R,
      gE.euclideanCoefficients x = g.pullbackCoefficients e x)
    (hB : gE.euclideanCoefficients 0 = innerSL ℝ)
    (hρ : gE.pullbackVolumeDensity id 0 = 1) (k : ℕ)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < δ →
      ∀ (u W F : M → ℝ),
      (∀ x ∈ ball (0 : E3) R \ {0},
        ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ u (e x)) →
      (∀ x ∈ ball (0 : E3) R \ {0},
        ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ W (e x)) →
      (∀ x ∈ ball (0 : E3) R \ {0},
        ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ F (e x)) →
      (∀ n ≤ k, ∀ z ∈ sourceAnnulus,
        ‖iteratedFDeriv ℝ n (fun y => u (e (r • y))) z‖ ≤ A) →
      (∀ x ∈ ball (0 : E3) R \ {0},
        -8 * g.leviCivitaData.laplacian W (e x) +
          (g.leviCivitaData.scalarCurvature (e x) - 30 * u (e x) ^ 4) * W (e x) = F (e x)) →
      derivativeProfile 2 innerAnnulus (k + 2) (fun z => W (e (r • z))) ≤
        ENNReal.ofReal C *
          (derivativeProfile 2 sourceAnnulus 0 (fun z => W (e (r • z))) +
            derivativeProfile 2 sourceAnnulus k
              (fun z => r ^ 2 * gE.pullbackVolumeDensity id (r • z) * (F (e (r • z)) / 8))) := by
  obtain ⟨δa, hδa, L, hL, hmat⟩ :=
    exists_uniform_native_rescaled_bilinear_forms gE hB hρ (k + 2)
      (by norm_num : (0 : ℝ) < 3)
  obtain ⟨Q, hQ, hpot⟩ := exists_uniform_rescaledNativeJacobianPotential_jets gE k hA
  obtain ⟨C, hC, hest⟩ := exists_local_uniform_derivativeProfile_add_two_with_potential
    k outerAnnulus_open sourceAnnulus_open sourceAnnulus_precompact
    closure_sourceAnnulus_subset_outer closure_sourceAnnulus_subset_ball
    innerAnnulus_open innerAnnulus_precompact closure_innerAnnulus_subset_source
    (by norm_num : (0 : ℝ) < 1 / 2) hL hQ
  let δ := min 1 (min δa (R / 2))
  refine ⟨δ, C, lt_min zero_lt_one (lt_min hδa (by positivity)), hC, ?_⟩
  intro r hr hrδ u W F hu hW hF hujet hP
  have hr1 : r ≤ 1 := (hrδ.trans_le (min_le_left _ _)).le
  have hra : r < δa := hrδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrR : r * 2 < R := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp
    (hrδ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  let O : Set E3 := ball (0 : E3) R \ {0}
  have hO : IsOpen O := isOpen_ball.sdiff isClosed_singleton
  have hOs : O ⊆ e.source := fun _ hx => hsource (ball_subset_closedBall hx.1)
  have hOc : ∀ x ∈ O, gE.euclideanCoefficients x = g.pullbackCoefficients e x :=
    fun x hx => hcoeff x (ball_subset_closedBall hx.1)
  have hmap : MapsTo (fun z : E3 => r • z) outerAnnulus O := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [outerAnnulus, h] at hz
    refine ⟨?_, smul_ne_zero hr.ne' hz0⟩
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
    exact (mul_lt_mul_of_pos_left hz.2 hr).trans hrR
  have hus : ContDiffOn ℝ ∞ (fun z => u (e (r • z))) outerAnnulus :=
    (contDiffOn_native_chart_representative e he hOs hu).comp
      (contDiff_id.const_smul r).contDiffOn hmap
  have hWs : ContDiffOn ℝ ∞ (fun z => W (e (r • z))) outerAnnulus :=
    (contDiffOn_native_chart_representative e he hOs hW).comp
      (contDiff_id.const_smul r).contDiffOn hmap
  have hFs : ContDiffOn ℝ ∞ (fun z => F (e (r • z))) outerAnnulus :=
    (contDiffOn_native_chart_representative e he hOs hF).comp
      (contDiff_id.const_smul r).contDiffOn hmap
  let q := rescaledNativeJacobianPotential gE r (fun z => u (e (r • z)))
  let f : E3 → ℝ := fun z => r ^ 2 * gE.pullbackVolumeDensity id (r • z) *
    (F (e (r • z)) / 8)
  have hρs : ContDiff ℝ ∞ (fun z : E3 => gE.pullbackVolumeDensity id (r • z)) :=
    (native_density_smooth_positive gE).1.comp (contDiff_id.const_smul r)
  have hRs : ContDiff ℝ ∞ (fun z : E3 => gE.leviCivitaData.scalarCurvature (r • z)) :=
    gE.leviCivitaData.contMDiff_scalarCurvature.contDiff.comp (contDiff_id.const_smul r)
  have hqs : ContDiffOn ℝ ∞ q outerAnnulus :=
    (contDiffOn_const.mul hρs.contDiffOn).mul
      ((hRs.contDiffOn.sub (contDiffOn_const.mul (hus.pow 4))).div_const 8)
  have hfs : ContDiffOn ℝ ∞ f outerAnnulus :=
    (contDiffOn_const.mul hρs.contDiffOn).mul (hFs.div_const 8)
  have hqj : ∀ n ≤ k, ∀ z ∈ sourceAnnulus, ‖iteratedFDeriv ℝ n q z‖ ≤ Q := by
    intro n hn z hz
    have hzO := closure_sourceAnnulus_subset_outer (subset_closure hz)
    have hv : ContDiffAt ℝ k (fun y => u (e (r • y))) z :=
      (hus.contDiffAt (outerAnnulus_open.mem_nhds hzO)).of_le (by exact_mod_cast le_top)
    have hj := hpot r ⟨hr.le, hr1⟩ _ z (by linarith [hz.1]) (by linarith [hz.2])
      hv (fun i hi => hujet i hi z hz) n hn
    exact hj.trans (mul_le_of_le_one_right hQ (pow_le_one₀ hr.le hr1))
  obtain ⟨B, hBa, hBlam, hBj, hBosc⟩ := hmat r hr.le hra
  have hVball : sourceAnnulus ⊆ ball (0 : E3) 3 :=
    subset_closure.trans closure_sourceAnnulus_subset_ball
  have hweak : WeakEquation sourceAnnulus
      (matrixFlux B.a (fun j => partialDeriv j (fun z => W (e (r • z)))))
      (fun z => f z + q z * W (e (r • z))) := by
    rw [hBa]
    exact native_jacobian_rescaled_weak_equation g gE g.leviCivitaData gE.leviCivitaData
      e he hei hO outerAnnulus_open sourceAnnulus_open sourceAnnulus_precompact
      closure_sourceAnnulus_subset_outer hOs hOc hW hP r hmap
  exact hest B (by rw [hBlam])
    (fun n hn z hz i j => hBj n hn z (hVball hz) i j)
    (fun z hz => hBosc z (hVball hz)) q hqs hqj hWs hfs hweak

#print axioms exists_uniform_native_chart_jacobian_annular_bound

end Yamabe3.Analysis.NativeJacobianAnnulus
