import Yamabe3.Analysis.NativeHalfAllScaleGeometricRows
import Yamabe3.Analysis.NativeLogShellPartition

/-! Operator-norm summation of the actual weighted-adjoint returns of
shrinking-collar errors. This constructs a source feedback and its exact
pairing, not yet the full native equation or low-mode compensation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

variable (P : NativeHighPotential)
  (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

def nativeGeometricSourceTerm (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) (n : ℕ) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ]
      Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) :=
  (nativeShellSourceReturnCLM (nativeLogShellCenter n)).comp
    (nativeL2HalfGeometricRowCLM P hplus g ε v hv phase (nativeLogShellCenter n))

def nativeGlobalGeometricSourceCLM (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) →L[ℝ]
      Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) :=
  ∑' n,nativeGeometricSourceTerm P hplus g ε v hv phase n

theorem exists_nativeGeometricSourceTerm_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0 < C ∧ ∀ ε : ℝ,0 ≤ ε → ε ≤ 1 → ∀ p ∈ Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) → ∀ phase n,
      ‖nativeGeometricSourceTerm P hplus (g p) ε v hv phase n‖ ≤
        C*ε*Real.exp (-nativeLogShellCenter n) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeL2Half_geometric_row_decay P hplus Λ g hB hρ
  let L := ‖nativeL2HighPhysicalSourceCLM‖*Real.exp 1
  have hL : 0≤L := by positivity
  refine ⟨(L+1)*C,by positivity,fun ε hε hε1 p hp v hv hvb hvo phase n => ?_⟩
  have ht := ContinuousLinearMap.opNorm_comp_le
    (nativeShellSourceReturnCLM (nativeLogShellCenter n))
    (nativeL2HalfGeometricRowCLM P hplus (g p) ε v hv phase (nativeLogShellCenter n))
  have hr := hc ε hε hε1 p hp v hv hvb hvo phase (nativeLogShellCenter n)
    (nativeLogShellCenter_nonneg n)
  apply ht.trans
  have hb := mul_le_mul (nativeShellSourceReturn_norm (nativeLogShellCenter n)) hr
    (norm_nonneg _) hL
  apply hb.trans
  change L*(C*ε*Real.exp (-nativeLogShellCenter n))≤_
  nlinarith [Real.exp_pos (-nativeLogShellCenter n),mul_nonneg hC.le hε]

theorem nativeGeometricSourceTerm_summable
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (p : ι) (hp : p∈Λ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (hvb : ∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2)
    (hvo : ∀ t,deriv (deriv v) t=radialForce (v t)) (phase : ℝ) :
    Summable (nativeGeometricSourceTerm P hplus (g p) ε v hv phase) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeGeometricSourceTerm_bound P hplus Λ g hB hρ
  exact (nativeLogShell_decay_summable.mul_left (C*ε)).of_norm_bounded
    (hc ε hε hε1 p hp v hv hvb hvo phase)

theorem exists_nativeGlobalGeometricSource_norm_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p ∈ Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p ∈ Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0 < C ∧ ∀ ε : ℝ,0 ≤ ε → ε ≤ 1 → ∀ p ∈ Λ,
      ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v),
      (∀ t,0 ≤ v t ∧ v t ≤ 1 ∧ |deriv v t| ≤ 1/2) →
      (∀ t,deriv (deriv v) t=radialForce (v t)) → ∀ phase,
      ‖nativeGlobalGeometricSourceCLM P hplus (g p) ε v hv phase‖ ≤ C*ε := by
  obtain ⟨C,hC,hc⟩ := exists_nativeGeometricSourceTerm_bound P hplus Λ g hB hρ
  let S := Real.exp (-(1/4:ℝ))*(1-Real.exp (-(1/2:ℝ)))⁻¹
  have hS : 0<S := by
    dsimp only [S]
    exact mul_pos (Real.exp_pos _) (inv_pos.mpr (sub_pos.mpr
      (Real.exp_lt_one_iff.mpr (by norm_num))))
  refine ⟨C*S,by positivity,fun ε hε hε1 p hp v hv hvb hvo phase => ?_⟩
  have hb := tsum_of_norm_bounded
    ((nativeLogShell_decay_summable.hasSum).mul_left (C*ε))
    (hc ε hε hε1 p hp v hv hvb hvo phase)
  rw [nativeLogShell_decay_sum] at hb
  exact hb.trans_eq (by dsimp only [S];ring)

#print axioms exists_nativeGeometricSourceTerm_bound
#print axioms nativeGeometricSourceTerm_summable
#print axioms exists_nativeGlobalGeometricSource_norm_bound
end Yamabe3.Analysis.SpherePolar
