import Yamabe3.Analysis.LinearDilatedJetDecay
import Yamabe3.Analysis.NativeFullCollarJetError

/-! Quantitative radius decay of the actual native geometric error.
The coefficient is fixed before scale, orbit, phase and the input jet;
this estimate supplies a summable factor on shrinking collars. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT Metric
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic Delaunay Yamabe3.Analysis.GreenParametrix
open Poincare.Analysis.Elliptic.Iteration Poincare.Analysis.Elliptic.InteriorEstimates

theorem exists_native_principal_collar_error_linear_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0 < C ∧ ∀ r : ℝ,0 ≤ r → r ≤ 1 → ∀ p ∈ Λ,∀ J : NativeCollarJet,
      ‖nativeCollarGeometricErrorCLM (g p) r J‖ ≤ (C*r)*‖J‖ := by
  classical
  let f : (Λ × Fin 3 × Fin 3) → E → ℝ := fun q x =>
    nativeDivergenceMatrix (g q.1) x q.2.1 q.2.2-(1 : Matrix (Fin 3) (Fin 3) ℝ) q.2.1 q.2.2
  have hf (q : Λ × Fin 3 × Fin 3) : ContDiff ℝ ∞ (f q) :=
    (contDiff_nativeDivergenceMatrix (g q.1) q.2.1 q.2.2).sub contDiff_const
  have hf0 (q : Λ × Fin 3 × Fin 3) : f q 0=0 := by
    dsimp [f]
    rw [nativeDivergenceMatrix_zero (g q.1) (hB q.1 q.1.property) (hρ q.1 q.1.property)]
    exact sub_self _
  obtain ⟨C,hC,h⟩ := exists_linear_finite_rescaled_zero_jet_bound f hf hf0 1 (by norm_num : (0:ℝ) < 2)
  refine ⟨39*C,by positivity,fun r hr hr1 p hp J => ?_⟩
  have hA (n : ℕ) (hn : n ≤ 1) (x : E) (hx : x ∈ nativePoissonEntranceCollar) (i j : Fin 3) :
      ‖iteratedFDeriv ℝ n (nativeScaledPrincipalError (g p) r i j) x‖ ≤ C*r :=
    h r hr hr1 (⟨p,hp⟩,i,j) n hn x (by simpa only [mem_closedBall,dist_zero_right] using (nativeEntranceCollar_annular hx).2)
  have ha (x : E) (hx : x ∈ nativePoissonEntranceCollar) (i j : Fin 3) :
      ‖nativeScaledPrincipalError (g p) r i j x‖ ≤ 3*C*r := by
    have hh : ‖nativeScaledPrincipalError (g p) r i j x‖ ≤ C*r := by
      simpa only [norm_iteratedFDeriv_zero] using hA 0 (by omega) x hx i j
    nlinarith [mul_nonneg hC.le hr]
  have hb (x : E) (hx : x ∈ nativePoissonEntranceCollar) (j : Fin 3) :
      ‖nativeScaledFirstError (g p) r j x‖ ≤ 3*C*r := by
    unfold nativeScaledFirstError
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin 3,C*r := by
        apply Finset.sum_le_sum
        intro i _
        have hder := (Poincare.Analysis.Sobolev.Euclidean.norm_iteratedFDeriv_partial_le (contDiff_nativeScaledPrincipalError (g p) r i j) i 0 x).trans
          (hA 1 (by omega) x hx i j)
        simpa only [norm_iteratedFDeriv_zero,Poincare.Analysis.Elliptic.Iteration.partialDeriv] using hder
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  have hh := nativeCollarJetPerturbationCLM_norm_le (nativeScaledPrincipalError (g p) r)
    (nativeScaledFirstError (g p) r) (fun _ => 0)
    (fun i j => (contDiff_nativeScaledPrincipalError (g p) r i j).continuous)
    (fun j => (contDiff_nativeScaledFirstError (g p) r j).continuous) continuous_const
    (by positivity : (0:ℝ) ≤ 3*C*r) ha hb (fun x hx => by simp;positivity) J
  exact hh.trans_eq (by ring)

theorem exists_native_potential_collar_error_linear_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0 < C ∧ ∀ r : ℝ,0 ≤ r → r ≤ 1 → ∀ p ∈ Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) →
      ∀ (phase : ℝ) (U : NativeCollarL2),
      ‖nativeCollarPotentialErrorCLM (g p) r v hv phase U‖ ≤ (C*r)*‖U‖ := by
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
  obtain ⟨Q,hQ,hq⟩ := exists_uniform_delaunay_annular_potential_jets 0
  refine ⟨L+Cρ*Q,by positivity,fun r hr hr1 p hp v hv hvb hvo phase U => ?_⟩
  apply nativeCollarLocalMulCLM_norm_le _ _ (by positivity)
  intro x hx
  have hx' := nativeEntranceCollar_annular hx
  have hrx : r • x ∈ closedBall (0:E) 2 := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hr]
    exact (mul_le_of_le_one_left (norm_nonneg x) hr1).trans hx'.2
  have hρx : ‖(g p).pullbackVolumeDensity id (r • x)-1‖ ≤ Cρ*r := by
    simpa only [norm_iteratedFDeriv_zero] using hρb r hr hr1 ⟨p,hp⟩ 0 le_rfl x
      (by simpa only [mem_closedBall,dist_zero_right] using hx'.2)
  have hqx : ‖annularDelaunayPotential v phase x‖ ≤ Q := by
    simpa only [norm_iteratedFDeriv_zero] using hq v hv hvb hvo phase 0 le_rfl x hx'.1 hx'.2
  unfold nativeDelaunayPotentialError
  calc
    _ ≤ r^2*‖nativePotentialDensity (g p) (r • x)‖+
        ‖(g p).pullbackVolumeDensity id (r • x)-1‖*‖annularDelaunayPotential v phase x‖ := by
      have hh := norm_add_le (r^2*nativePotentialDensity (g p) (r • x))
        (((g p).pullbackVolumeDensity id (r • x)-1)*annularDelaunayPotential v phase x)
      have he : ‖r^2*nativePotentialDensity (g p) (r • x)‖=r^2*‖nativePotentialDensity (g p) (r • x)‖ := by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg r),←Real.norm_eq_abs]
      rw [he,norm_mul] at hh
      exact hh
    _ ≤ r^2*L+(Cρ*r)*Q := add_le_add (mul_le_mul_of_nonneg_left (hSb ⟨p,hp⟩ (r • x) hrx) (sq_nonneg r))
      (mul_le_mul hρx hqx (norm_nonneg _) (by positivity))
    _ ≤ (L+Cρ*Q)*r := by nlinarith [mul_le_mul_of_nonneg_right (show r^2 ≤ r by nlinarith) hL.le]

theorem exists_native_full_collar_error_linear_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0 < C ∧ ∀ r : ℝ,0 ≤ r → r ≤ 1 → ∀ p ∈ Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) →
      ∀ (phase : ℝ) (J : NativeCollarJet),
      ‖nativeFullCollarJetErrorCLM (g p) r v hv phase J‖ ≤ (C*r)*‖J‖ := by
  obtain ⟨C,hC,hc⟩ := exists_native_principal_collar_error_linear_bound Λ g hB hρ
  obtain ⟨D,hD,hd⟩ := exists_native_potential_collar_error_linear_bound Λ g hρ
  refine ⟨C+D,by positivity,fun r hr hr1 p hp v hv hb ho phase J => ?_⟩
  have h0 := hc r hr hr1 p hp J
  have h1 := (hd r hr hr1 p hp v hv hb ho phase J.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le J) (by positivity))
  change ‖-nativeCollarGeometricErrorCLM (g p) r J+nativeCollarPotentialErrorCLM (g p) r v hv phase J.1‖ ≤ _
  calc
    _ ≤ ‖nativeCollarGeometricErrorCLM (g p) r J‖+‖nativeCollarPotentialErrorCLM (g p) r v hv phase J.1‖ := by
      simpa only [norm_neg] using norm_add_le (-nativeCollarGeometricErrorCLM (g p) r J)
        (nativeCollarPotentialErrorCLM (g p) r v hv phase J.1)
    _ ≤ _ := (add_le_add h0 h1).trans_eq (by ring)

#print axioms exists_native_principal_collar_error_linear_bound
#print axioms exists_native_potential_collar_error_linear_bound
#print axioms exists_native_full_collar_error_linear_bound
end Yamabe3.Analysis.SpherePolar
