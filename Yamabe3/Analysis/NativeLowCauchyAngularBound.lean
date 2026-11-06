import Yamabe3.Analysis.NativeLowCauchyUniformHalfEnd

/-! The computed finite low Cauchy correction has a uniform angular
bound before choosing its data. It is retained in the far exterior
estimate rather than silently omitted by a high-mode projection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativeLowCauchyCurve {τ:ℝ} (ht:0<τ) (v:NativeLowCauchyCoordinates) (t:ℝ) :AngularL2 :=
  ∑i∈nativeLowIndexFinset,nativeLowCauchyQ ht v i (τ+t) • angularBasis i

theorem nativeLowCauchyCurve_continuous {τ:ℝ} (ht:0<τ) (v:NativeLowCauchyCoordinates) :
    Continuous (nativeLowCauchyCurve ht v) := by
  apply continuous_finsetSum
  intro i hi
  exact (((nativeLowCauchyQ_C2 ht v i hi).continuous).comp (continuous_const.add continuous_id)).smul continuous_const

theorem nativeLowCauchyCurve_ae {τ:ℝ} (ht:0<τ) (v:NativeLowCauchyCoordinates) (t:ℝ) :
    (fun θ:S=>finiteAngular nativeLowIndexFinset (fun i s=>nativeLowCauchyQ ht v i (τ+s)) (t,θ))=ᵐ[angularVolume]
      (nativeLowCauchyCurve ht v t:S→ℝ) :=
  finiteAngular_ae nativeLowIndexFinset _ t

theorem exists_nativeLowCauchyCurve_halfLine_bound {τ:ℝ} (ht:0<τ) (c:ℝ) :
    ∃C:ℝ,0≤C ∧ ∀(v:NativeLowCauchyCoordinates) (t:ℝ),t≤c→‖nativeLowCauchyCurve ht v t‖≤C*‖v‖ := by
  classical
  let B:AngularIndex→ℝ:=fun i=>if hi:i∈nativeLowIndexFinset then
    (bubbleLowZeroCauchyLinear_halfLine_bound i hi ht (τ+c)).choose else 0
  have hB (i:AngularIndex) (hi:i∈nativeLowIndexFinset):0≤B i:=by
    dsimp only [B];rw [dif_pos hi]
    exact (bubbleLowZeroCauchyLinear_halfLine_bound i hi ht (τ+c)).choose_spec.1
  refine ⟨∑i∈nativeLowIndexFinset,B i,Finset.sum_nonneg hB,fun v t ht' =>?_⟩
  calc
    ‖nativeLowCauchyCurve ht v t‖ ≤ ∑i∈nativeLowIndexFinset,‖nativeLowCauchyQ ht v i (τ+t) • angularBasis i‖ := norm_sum_le _ _
    _ ≤ ∑i∈nativeLowIndexFinset,B i*‖v‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul,angularBasis.orthonormal.norm_eq_one i,mul_one]
      have hh:=(bubbleLowZeroCauchyLinear_halfLine_bound i hi ht (τ+c)).choose_spec.2
        (v ⟨i,hi⟩).1 (v ⟨i,hi⟩).2 (τ+t) (by linarith only [ht'])
      have hn:max ‖(v ⟨i,hi⟩).1‖ ‖(v ⟨i,hi⟩).2‖≤‖v‖:=by
        simpa only [Prod.norm_def] using norm_le_pi_norm v ⟨i,hi⟩
      change ‖nativeLowCauchyQ ht v i (τ+t)‖≤_
      rw [nativeLowCauchyQ,dif_pos hi]
      apply hh.1.trans
      have hBi:(bubbleLowZeroCauchyLinear_halfLine_bound i hi ht (τ+c)).choose=B i:=by
        dsimp only [B];rw [dif_pos hi]
      rw [hBi]
      exact mul_le_mul_of_nonneg_left hn (hB i hi)
    _ = _ := (Finset.sum_mul _ _ _).symm

#print axioms nativeLowCauchyCurve_continuous
#print axioms nativeLowCauchyCurve_ae
#print axioms exists_nativeLowCauchyCurve_halfLine_bound
end Yamabe3.Analysis.SpherePolar
