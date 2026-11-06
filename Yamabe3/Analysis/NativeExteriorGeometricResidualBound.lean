import Yamabe3.Analysis.NativeExteriorGeometricResidual

/-! Uniform actual exterior geometric residual bounds. The potential
bound and finite metric family precede the radius and the input jet. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Delaunay Yamabe3.Analysis.GreenParametrix
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem exists_native_bcf_potential_collar_error_linear_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1)
    {M : ℝ} (hM : 0≤M) :
    ∃ C : ℝ,0 < C ∧ ∀ r : ℝ,0 ≤ r → r ≤ 1 → ∀ p ∈ Λ,
      ∀ (V : ℝ →ᵇ ℝ),‖V‖≤M → ∀ U : NativeCollarL2,
      ‖nativeCollarLocalMulCLM (nativeBCFPotentialError (g p) r V)
        (nativeBCFPotentialError_continuousOn (g p) r V) U‖ ≤ (C*r)*‖U‖ := by
  classical
  let f : Λ → E → ℝ := fun p x => (g p).pullbackVolumeDensity id x-1
  have hf (p : Λ) : ContDiff ℝ ∞ (f p) := (native_density_smooth_positive (g p)).1.sub contDiff_const
  have hf0 (p : Λ) : f p 0=0 := by dsimp [f];rw [hρ p p.property];ring
  obtain ⟨Cρ,hCρ,hρb⟩ := exists_linear_finite_rescaled_zero_jet_bound f hf hf0 0 (by norm_num : (0:ℝ) < 2)
  have hS : ∀ p : Λ,∃ C : ℝ,∀ x ∈ closedBall (0:E) 2,‖nativePotentialDensity (g p) x‖ ≤ C := by
    intro p
    exact (isCompact_closedBall (0:E) 2).exists_bound_of_continuousOn (contDiff_nativePotentialDensity (g p)).continuous.continuousOn
  choose S hS using hS
  let L := 1+∑ p : Λ,max 0 (S p)
  have hsum : 0 ≤ ∑ p : Λ,max 0 (S p) := Finset.sum_nonneg (fun p _ => le_max_left _ _)
  have hL : 0 < L := by dsimp only [L];linarith
  have hSb (p : Λ) (x : E) (hx : x ∈ closedBall (0:E) 2) : ‖nativePotentialDensity (g p) x‖ ≤ L := by
    have hs := Finset.single_le_sum (fun q _ => le_max_left (0:ℝ) (S q)) (Finset.mem_univ p)
    exact ((hS p x hx).trans (le_max_right _ _)).trans (hs.trans (by dsimp only [L];linarith))
  let Q := M*Real.exp 1
  have hQ : 0≤Q := mul_nonneg hM (Real.exp_pos _).le
  refine ⟨L+Cρ*Q,by positivity,fun r hr hr1 p hp V hV U => ?_⟩
  apply nativeCollarLocalMulCLM_norm_le _ _ (by positivity)
  intro x hx
  have hx' := nativeEntranceCollar_annular hx
  have hrx : r • x ∈ closedBall (0:E) 2 := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hr]
    exact (mul_le_of_le_one_left (norm_nonneg x) hr1).trans hx'.2
  have hρx : ‖(g p).pullbackVolumeDensity id (r • x)-1‖ ≤ Cρ*r := by
    simpa only [norm_iteratedFDeriv_zero] using hρb r hr hr1 ⟨p,hp⟩ 0 le_rfl x
      (by simpa only [mem_closedBall,dist_zero_right] using hx'.2)
  have hqx : ‖nativeHalfEndPotentialCoefficient V x‖≤Q :=
    (nativeCollarPotential_bound V hx).trans (mul_le_mul_of_nonneg_right hV (Real.exp_pos _).le)
  unfold nativeBCFPotentialError
  calc
    _ ≤ r^2*‖nativePotentialDensity (g p) (r • x)‖+
        ‖(g p).pullbackVolumeDensity id (r • x)-1‖*‖nativeHalfEndPotentialCoefficient V x‖ := by
      have hh := norm_sub_le (r^2*nativePotentialDensity (g p) (r • x))
        (((g p).pullbackVolumeDensity id (r • x)-1)*nativeHalfEndPotentialCoefficient V x)
      have he : ‖r^2*nativePotentialDensity (g p) (r • x)‖=r^2*‖nativePotentialDensity (g p) (r • x)‖ := by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg r),←Real.norm_eq_abs]
      rw [he,norm_mul] at hh
      exact hh
    _ ≤ r^2*L+(Cρ*r)*Q := add_le_add (mul_le_mul_of_nonneg_left (hSb ⟨p,hp⟩ (r • x) hrx) (sq_nonneg r))
      (mul_le_mul hρx hqx (norm_nonneg _) (by positivity))
    _ ≤ (L+Cρ*Q)*r := by nlinarith [mul_le_mul_of_nonneg_right (show r^2 ≤ r by nlinarith) hL.le]

theorem exists_native_bcf_full_collar_error_linear_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) {M : ℝ} (hM : 0≤M) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0≤r → r≤1 → ∀p∈Λ,∀V : ℝ →ᵇ ℝ,‖V‖≤M → ∀J : NativeCollarJet,
      ‖nativeBCFCollarErrorCLM (g p) r V J‖≤(C*r)*‖J‖ := by
  obtain ⟨C,hC,hc⟩ := exists_native_principal_collar_error_linear_bound Λ g hB hρ
  obtain ⟨D,hD,hd⟩ := exists_native_bcf_potential_collar_error_linear_bound Λ g hρ hM
  refine ⟨C+D,by positivity,fun r hr hr1 p hp V hV J => ?_⟩
  have h0 := hc r hr hr1 p hp J
  have h1 := (hd r hr hr1 p hp V hV J.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le J) (by positivity))
  change ‖-nativeCollarGeometricErrorCLM (g p) r J+
    nativeCollarLocalMulCLM (nativeBCFPotentialError (g p) r V) (nativeBCFPotentialError_continuousOn (g p) r V) J.1‖≤_
  calc
    _≤‖nativeCollarGeometricErrorCLM (g p) r J‖+
        ‖nativeCollarLocalMulCLM (nativeBCFPotentialError (g p) r V) (nativeBCFPotentialError_continuousOn (g p) r V) J.1‖ := by
      simpa only [norm_neg] using norm_add_le (-nativeCollarGeometricErrorCLM (g p) r J)
        (nativeCollarLocalMulCLM (nativeBCFPotentialError (g p) r V) (nativeBCFPotentialError_continuousOn (g p) r V) J.1)
    _≤_ := (add_le_add h0 h1).trans_eq (by ring)

theorem exists_native_exterior_geometric_residual_linear_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) {M : ℝ} (hM : 0≤M) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0≤r → r≤1 → ∀p∈Λ,∀V : ℝ →ᵇ ℝ,‖V‖≤M → ∀J : NativeCollarJet,
      ‖nativeExteriorGeometricResidualCLM (g p) r V J‖≤(C*r)*‖J‖ := by
  obtain ⟨C,hC,hc⟩ := exists_native_bcf_full_collar_error_linear_bound Λ g hB hρ hM
  refine ⟨8*C,by positivity,fun r hr hr1 p hp V hV J => ?_⟩
  change ‖(8:ℝ) • nativeNegativeCollarRestrictionCLM (nativeBCFCollarErrorCLM (g p) r V J)‖≤_
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤8)]
  have h := l2MeasureRestrict_norm_le (ν := volume.restrict nativeNegativeEntranceCollar) (Measure.restrict_mono inter_subset_left le_rfl)
    (nativeBCFCollarErrorCLM (g p) r V J)
  exact (mul_le_mul_of_nonneg_left (h.trans (hc r hr hr1 p hp V hV J)) (by norm_num : (0:ℝ)≤8)).trans_eq (by ring)

#print axioms exists_native_bcf_potential_collar_error_linear_bound
#print axioms exists_native_bcf_full_collar_error_linear_bound
#print axioms exists_native_exterior_geometric_residual_linear_bound
end Yamabe3.Analysis.SpherePolar
