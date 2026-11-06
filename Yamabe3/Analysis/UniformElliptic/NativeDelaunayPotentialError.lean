import Yamabe3.Analysis.UniformElliptic.NativeLocalSmallGeometricError
import Yamabe3.Analysis.UniformElliptic.NativeJacobianPotentialJets
import Yamabe3.Analysis.DelaunayAnnularPotentialJets
import Yamabe3.Analysis.Cylinder.NativeCylinderJacobi

/-!
# Small actual curved Delaunay potential error

The displayed error is the genuine density-weighted scalar-curvature term
plus the density defect times the literal Delaunay potential. Finite jets
are uniformly small before the bounded orbit and phase are selected.
The identity with the actual rescaled native Jacobian potential fixes its
sign, fourth power, density and radius factors.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT GreenParametrix Delaunay SpherePolar

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def nativeDelaunayPotentialError (g : RiemannianMetric 3 E3)
    (r : ℝ) (v : ℝ → ℝ) (τ : ℝ) (z : E3) : ℝ :=
  r ^ 2 * nativePotentialDensity g (r • z) +
    (g.pullbackVolumeDensity id (r • z) - 1) * annularDelaunayPotential v τ z

def delaunayRescaledBackground (v : ℝ → ℝ) (r τ : ℝ) (z : E3) : ℝ :=
  radialScale r * radialScale ‖z‖ * v (τ - Real.log ‖z‖)

theorem contDiffAt_annularDelaunayPotential {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (τ : ℝ) {z : E3} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (annularDelaunayPotential v τ) z := by
  have hn : ContDiffAt ℝ ∞ (fun y : E3 => ‖y‖) z := contDiffAt_norm ℝ hz
  have hl := (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hz)).comp z hn
  exact (contDiffAt_const.mul ((hv.contDiffAt.comp z
    (contDiffAt_const.sub hl)).pow 4)).div (hn.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))

theorem contDiffAt_nativeDelaunayPotentialError
    (g : RiemannianMetric 3 E3) (r : ℝ) {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (τ : ℝ) {z : E3} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (nativeDelaunayPotentialError g r v τ) z := by
  have hS := (contDiff_nativePotentialDensity g).comp (contDiff_id.const_smul r)
  have hρ := (native_density_smooth_positive g).1.comp (contDiff_id.const_smul r)
  exact (contDiffAt_const.mul hS.contDiffAt).add
    ((hρ.contDiffAt.sub contDiffAt_const).mul (contDiffAt_annularDelaunayPotential hv τ hz))

/-- This is exactly the native scaled Jacobian coefficient for the literal
same radial background, with the sign of the native weak equation. -/
theorem rescaledNativeJacobianPotential_delaunay
    (g : RiemannianMetric 3 E3) {r : ℝ} (hr : 0 < r)
    (v : ℝ → ℝ) (τ : ℝ) {z : E3} (hz : z ≠ 0) :
    rescaledNativeJacobianPotential g r (delaunayRescaledBackground v r τ) z =
      -(annularDelaunayPotential v τ z + nativeDelaunayPotentialError g r v τ z) := by
  have hs4 : radialScale r ^ 4 = (r ^ 2)⁻¹ := by
    rw [show radialScale r ^ 4 = (radialScale r ^ 2) ^ 2 by ring,
      radialScale_sq hr, inv_pow]
  have hz4 : radialScale ‖z‖ ^ 4 = (‖z‖ ^ 2)⁻¹ := by
    rw [show radialScale ‖z‖ ^ 4 = (radialScale ‖z‖ ^ 2) ^ 2 by ring,
      radialScale_sq (norm_pos_iff.mpr hz), inv_pow]
  simp only [rescaledNativeJacobianPotential, delaunayRescaledBackground,
    nativeDelaunayPotentialError, nativePotentialDensity, annularDelaunayPotential, mul_pow,
    hs4, hz4]
  field_simp [hr.ne', norm_ne_zero_iff.mpr hz]
  <;> ring

private theorem norm_scalar_scaled_jet {f : E3 → ℝ} {z : E3} {n : ℕ}
    (hf : ContDiffAt ℝ n f z) (c : ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => c * f y) z‖ =
      |c| * ‖iteratedFDeriv ℝ n f z‖ := by
  change ‖iteratedFDeriv ℝ n (c • f) z‖ = _
  rw [iteratedFDeriv_const_smul_apply hf, norm_smul, Real.norm_eq_abs]

/-- All finite jets are uniformly small for this fixed native metric;
the radius precedes the actual orbit, its phase and the annular point. -/
theorem exists_uniform_small_native_delaunay_potential_error
    (g : RiemannianMetric 3 E3) (hρ0 : g.pullbackVolumeDensity id 0 = 1)
    (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ →
      ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
        (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1 / 2) →
        (∀ t, deriv (deriv v) t = radialForce (v t)) →
        ∀ (τ : ℝ) (n : ℕ), n ≤ k → ∀ z : E3,
          (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
          ‖iteratedFDeriv ℝ n (nativeDelaunayPotentialError g r v τ) z‖ ≤ η := by
  obtain ⟨Cq, hCq, hq⟩ := exists_uniform_delaunay_annular_potential_jets k
  have hS := contDiff_nativePotentialDensity g
  obtain ⟨CS, hCS, hSj⟩ := exists_uniform_spatial_jet_bounds
    (fun q (_hq : q.2 ≠ 0) => hS.contDiffAt.comp q
      (contDiffAt_fst.smul contDiffAt_snd)) k
  let L : ℝ := (2 : ℝ) ^ k * (Cq + 1)
  have hL : 0 < L := mul_pos (by positivity) (by linarith)
  let α : ℝ := η / (2 * L)
  have hα : 0 < α := div_pos hη (mul_pos (by norm_num) hL)
  obtain ⟨d, hd, hdρ⟩ := exists_small_rescaled_zero_jets
    ((native_density_smooth_positive g).1.sub contDiff_const)
    (show g.pullbackVolumeDensity id 0 - 1 = 0 by rw [hρ0]; ring) k
    (by norm_num : (0 : ℝ) < 2) hα
  let δ := min d (min 1 (η / (2 * (CS + 1))))
  have hδ : 0 < δ := lt_min hd (lt_min (by norm_num)
    (div_pos hη (by nlinarith only [hCS])))
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ v hv hb hODE τ n hn z hzlo hzup
  have hrd : r < d := hrδ.trans_le (min_le_left _ _)
  have hr1 : r ≤ 1 := (hrδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hrη : r * (2 * (CS + 1)) < η := (lt_div_iff₀ (by nlinarith only [hCS])).mp
    (hrδ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hzlo)
  have hzball : z ∈ closedBall (0 : E3) 2 := by
    simpa only [mem_closedBall, dist_zero_right] using hzup
  let Sr : E3 → ℝ := fun y => nativePotentialDensity g (r • y)
  let dr : E3 → ℝ := fun y => g.pullbackVolumeDensity id (r • y) - 1
  let q : E3 → ℝ := annularDelaunayPotential v τ
  have hSr : ContDiff ℝ ∞ Sr := hS.comp (contDiff_id.const_smul r)
  have hdr : ContDiff ℝ ∞ dr :=
    ((native_density_smooth_positive g).1.comp (contDiff_id.const_smul r)).sub contDiff_const
  have hqz : ContDiffAt ℝ ∞ q z := contDiffAt_annularDelaunayPotential hv τ hz0
  have hdk : ContDiffAt ℝ k dr z := hdr.contDiffAt.of_le (by exact_mod_cast le_top)
  have hqk : ContDiffAt ℝ k q z := hqz.of_le (by exact_mod_cast le_top)
  have hprod : ‖iteratedFDeriv ℝ n (fun y => dr y * q y) z‖ ≤ η / 2 := by
    have h := norm_iteratedFDeriv_mul_le_of_local_jets hdk hqk hα.le hCq
      (fun i hi => hdρ r hr hrd i hi z hzball)
      (fun i hi => hq v hv hb hODE τ i hi z hzlo hzup) hn
    have hnum : (2 : ℝ) ^ k * α * Cq ≤ η / 2 := by
      dsimp only [α, L]
      have hpow : (0 : ℝ) < 2 ^ k := by positivity
      field_simp
      nlinarith [mul_nonneg hη.le hpow.le]
    exact h.trans hnum
  have hscalar : ‖iteratedFDeriv ℝ n (fun y => r ^ 2 * Sr y) z‖ ≤ η / 2 := by
    rw [norm_scalar_scaled_jet (hSr.contDiffAt.of_le (by exact_mod_cast le_top)),
      abs_of_nonneg (sq_nonneg r)]
    have hr2 : r ^ 2 ≤ r := by nlinarith only [hr, hr1]
    calc
      _ ≤ r ^ 2 * CS := mul_le_mul_of_nonneg_left (hSj n hn r ⟨hr, hr1⟩ z hzlo hzup) (sq_nonneg r)
      _ ≤ r * CS := mul_le_mul_of_nonneg_right hr2 hCS
      _ ≤ η / 2 := by nlinarith only [hrη, hr]
  change ‖iteratedFDeriv ℝ n (fun y => r ^ 2 * Sr y + dr y * q y) z‖ ≤ η
  rw [fun_iteratedFDeriv_add_apply
    ((contDiffAt_const.mul hSr.contDiffAt).of_le (by exact_mod_cast le_top))
    ((hdr.contDiffAt.mul hqz).of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans ((add_le_add hscalar hprod).trans_eq (by ring))

/-- One scale works for every member of the supplied finite metric family;
no extra orbit, phase or small-neck condition is introduced. -/
theorem exists_uniform_small_finite_native_delaunay_potential_error
    {ι : Type*} (Λ : Finset ι) (gE : ι → RiemannianMetric 3 E3)
    (hρ : ∀ p ∈ Λ, (gE p).pullbackVolumeDensity id 0 = 1)
    (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ → ∀ p ∈ Λ,
      ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v →
        (∀ t, 0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1 / 2) →
        (∀ t, deriv (deriv v) t = radialForce (v t)) →
        ∀ (τ : ℝ) (n : ℕ), n ≤ k → ∀ z : E3,
          (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 →
          ‖iteratedFDeriv ℝ n (nativeDelaunayPotentialError (gE p) r v τ) z‖ ≤ η := by
  classical
  choose d hd hb using fun p : Λ =>
    exists_uniform_small_native_delaunay_potential_error (gE p) (hρ p p.property) k hη
  have hevent : ∀ᶠ r : ℝ in 𝓝 0, ∀ p : Λ, r < d p :=
    eventually_all.mpr fun p => Iio_mem_nhds (hd p)
  obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ p hp
  exact hb ⟨p, hp⟩ r hr (hδb (by
    simpa only [mem_ball, dist_zero_right, Real.norm_of_nonneg hr] using hrδ) ⟨p, hp⟩)

#print axioms rescaledNativeJacobianPotential_delaunay
#print axioms exists_uniform_small_native_delaunay_potential_error
#print axioms exists_uniform_small_finite_native_delaunay_potential_error

end Yamabe3.Analysis.UniformElliptic
