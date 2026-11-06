import Yamabe3.Analysis.UniformElliptic.NativeScaledForcing
import Yamabe3.Analysis.UniformElliptic.LocalJetProducts

/-!
# Uniform jets of the actual rescaled Jacobian potential

The potential is exactly the native density times `(R - 30 v^4)/8`,
with the sign and scale from the true rescaled weak equation. Compactness
controls the fixed metric factors. Finite Leibniz estimates then convert
the actual local background jets into a bound chosen before the scale
and background. The resulting coefficient jets are O(r^2).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Filter
open scoped ContDiff Topology Manifold

namespace Yamabe3.Analysis.UniformElliptic

open PoincareMT GreenParametrix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The signed potential in the actual rescaled weak Jacobian equation.
`v` is the background already pulled back and rescaled in that equation. -/
def rescaledNativeJacobianPotential (g : RiemannianMetric 3 E3)
    (r : ℝ) (v : E3 → ℝ) (z : E3) : ℝ :=
  -r ^ 2 * g.pullbackVolumeDensity id (r • z) *
    ((g.leviCivitaData.scalarCurvature (r • z) - 30 * v z ^ 4) / 8)

private theorem norm_iteratedFDeriv_const_mul_local
    {f : E3 → ℝ} {z : E3} {n : ℕ} (hf : ContDiffAt ℝ n f z) (c : ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => c * f y) z‖ =
      |c| * ‖iteratedFDeriv ℝ n f z‖ := by
  change ‖iteratedFDeriv ℝ n (c • f) z‖ = _
  rw [iteratedFDeriv_const_smul_apply hf, norm_smul, Real.norm_eq_abs]

/-- Fixed metric data and an actual finite background-jet bound produce
the same potential's uniform finite jets. No scale-dependent elliptic
constant or independent potential field is an assumption. -/
theorem exists_uniform_rescaledNativeJacobianPotential_jets
    (g : RiemannianMetric 3 E3) (k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ r ∈ Icc (0 : ℝ) 1, ∀ (v : E3 → ℝ) (z : E3),
      (1 / 2 : ℝ) ≤ ‖z‖ → ‖z‖ ≤ 2 → ContDiffAt ℝ k v z →
      (∀ i ≤ k, ‖iteratedFDeriv ℝ i v z‖ ≤ A) →
      ∀ n ≤ k, ‖iteratedFDeriv ℝ n (rescaledNativeJacobianPotential g r v) z‖ ≤
        Q * r ^ 2 := by
  have hρ := (native_density_smooth_positive g).1
  have hS := contDiff_nativePotentialDensity g
  obtain ⟨Cρ, hCρ, hbρ⟩ := exists_uniform_spatial_jet_bounds
    (fun q (_hq : q.2 ≠ 0) => hρ.contDiffAt.comp q
      (contDiffAt_fst.smul contDiffAt_snd)) k
  obtain ⟨CS, hCS, hbS⟩ := exists_uniform_spatial_jet_bounds
    (fun q (_hq : q.2 ≠ 0) => hS.contDiffAt.comp q
      (contDiffAt_fst.smul contDiffAt_snd)) k
  let T : ℝ := (2 : ℝ) ^ k * Cρ * (((2 : ℝ) ^ k) ^ 3 * A ^ 4)
  have hT : 0 ≤ T := by unfold T; positivity
  refine ⟨CS + (30 / 8 : ℝ) * T, by positivity, ?_⟩
  intro r hr v z hzlo hzup hv hvj n hn
  let ρr : E3 → ℝ := fun y => g.pullbackVolumeDensity id (r • y)
  let Sr : E3 → ℝ := fun y => nativePotentialDensity g (r • y)
  let P : E3 → ℝ := fun y => ρr y * v y ^ 4
  have hρr : ContDiff ℝ ∞ ρr := hρ.comp (contDiff_id.const_smul r)
  have hSr : ContDiff ℝ ∞ Sr := hS.comp (contDiff_id.const_smul r)
  have hρrk : ContDiffAt ℝ k ρr z := hρr.contDiffAt.of_le (by exact_mod_cast le_top)
  have hPk : ContDiffAt ℝ k P z := hρrk.mul (hv.pow 4)
  have hPn : ContDiffAt ℝ n P z := hPk.of_le (by exact_mod_cast hn)
  have hSn : ContDiffAt ℝ n Sr z := hSr.contDiffAt.of_le (by exact_mod_cast le_top)
  have hPj : ‖iteratedFDeriv ℝ n P z‖ ≤ T :=
    norm_iteratedFDeriv_mul_le_of_local_jets hρrk (hv.pow 4) hCρ
      (by positivity : 0 ≤ ((2 : ℝ) ^ k) ^ 3 * A ^ 4)
      (fun i hi => hbρ i hi r hr z hzlo hzup)
      (fun i hi => norm_iteratedFDeriv_fourthPower_le_of_local_jets hv hA hvj hi) hn
  have hSj : ‖iteratedFDeriv ℝ n Sr z‖ ≤ CS := hbS n hn r hr z hzlo hzup
  have heq : rescaledNativeJacobianPotential g r v =
      (fun y => (-r ^ 2) * Sr y + ((30 / 8 : ℝ) * r ^ 2) * P y) := by
    funext y
    simp only [rescaledNativeJacobianPotential, Sr, P, ρr, nativePotentialDensity]
    ring
  rw [heq, fun_iteratedFDeriv_add_apply
    (contDiffAt_const.mul hSn) (contDiffAt_const.mul hPn)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (fun y => (-r ^ 2) * Sr y) z‖ +
        ‖iteratedFDeriv ℝ n (fun y => ((30 / 8 : ℝ) * r ^ 2) * P y) z‖ :=
      norm_add_le _ _
    _ = r ^ 2 * ‖iteratedFDeriv ℝ n Sr z‖ +
        ((30 / 8 : ℝ) * r ^ 2) * ‖iteratedFDeriv ℝ n P z‖ := by
      rw [norm_iteratedFDeriv_const_mul_local hSn,
        norm_iteratedFDeriv_const_mul_local hPn, abs_neg,
        abs_of_nonneg (sq_nonneg r), abs_of_nonneg (by positivity)]
    _ ≤ r ^ 2 * CS + ((30 / 8 : ℝ) * r ^ 2) * T :=
      add_le_add (mul_le_mul_of_nonneg_left hSj (sq_nonneg r))
        (mul_le_mul_of_nonneg_left hPj (by positivity))
    _ = _ := by ring

#print axioms exists_uniform_rescaledNativeJacobianPotential_jets

end Yamabe3.Analysis.UniformElliptic
