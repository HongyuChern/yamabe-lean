import Yamabe3.Analysis.NativeBubbleCompensationSobolev
import Yamabe3.Analysis.NativeCompensationCoefficientCLM
import Yamabe3.Analysis.NativeH4CorrectedMatchedField

/-! The same computed exterior compensation has a bounded H2 source
norm in the original model H4 input and correction operator norm. No
extra regularity or magnitude assumption is imposed on its coefficients. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Yamabe3.Analysis.UniformElliptic SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Euclidean

theorem exists_nativeBubbleCompensation_linear_bound {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (τ : ℝ) (k : ℕ) {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hO0 : closure O⊆({0}ᶜ : Set E)) (L : AngularIndex → H →L[ℝ] ℝ) :
    ∃C : ℝ≥0∞,C≠⊤ ∧ ∀x : H,
      MemWkp k 2 (nativeBubbleCollarCompensation τ (fun i => L i x)) O ∧
      iteratedWeakSobolevNorm k 2 (nativeBubbleCollarCompensation τ (fun i => L i x)) O≤C*ENNReal.ofReal ‖x‖ := by
  obtain ⟨A,hA,hb⟩ := exists_nativeBubbleCompensation_sobolev_bound τ k hO hOc hO0
  obtain ⟨B,hB,hL⟩ := exists_finite_coefficientCLM_bound nativeLowIndexFinset L
  refine ⟨A*ENNReal.ofReal B,by finiteness,?_⟩
  intro x
  have hh := hb (fun i => L i x) (B*‖x‖) (hL x)
  refine ⟨hh.1,?_⟩
  simpa only [ENNReal.ofReal_mul hB,mul_assoc] using hh.2

theorem exists_nativeH4Matched_compensation_bound
    (P : NativeHighPotential)
    (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
    (v : ℝ → ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
    (b : ℝ) {τ : ℝ} (ht : 0<τ) (k : ℕ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O)) (hO0 : closure O⊆({0}ᶜ : Set E)) :
    ∃ A B : ℝ≥0∞,A≠⊤ ∧ B≠⊤ ∧
      ∀ (T : HalfEndPhysicalH4Graph →L[ℝ] NativeTwoSidedSource) (Y : HalfEndPhysicalH4Graph),
      let q := fun x => nativeBubbleCollarCompensation τ
        (nativeCauchyCompensationData ht (nativeH4GraphAngularValueCLM Y) (nativeH4GraphAngularNormalCLM Y)) x+
        nativeBubbleCollarCompensation τ (nativeSupportedTwoSidedExteriorCompensation P hp v hv hb b ht (T Y)) x
      MemWkp k 2 q O ∧ iteratedWeakSobolevNorm k 2 q O≤
        (A+B*ENNReal.ofReal ‖T‖)*ENNReal.ofReal ‖Y‖ := by
  let L0 := fun i => (nativeCauchyCompensationCoefficientCLM τ i).comp
    (nativeH4GraphAngularValueCLM.prod nativeH4GraphAngularNormalCLM)
  let L1 := nativeSupportedCompensationCoefficientCLM P hp v hv hb b τ
  obtain ⟨A,hA,h0⟩ := exists_nativeBubbleCompensation_linear_bound τ k hO hOc hO0 L0
  obtain ⟨B,hB,h1⟩ := exists_nativeBubbleCompensation_linear_bound τ k hO hOc hO0 L1
  have he0 (Y : HalfEndPhysicalH4Graph) : (fun i => L0 i Y)=
      nativeCauchyCompensationData ht (nativeH4GraphAngularValueCLM Y) (nativeH4GraphAngularNormalCLM Y) := by
    funext i
    exact nativeCauchyCompensationCoefficientCLM_apply ht i _ _
  have he1 (X : NativeTwoSidedSource) : (fun i => L1 i X)=
      nativeSupportedTwoSidedExteriorCompensation P hp v hv hb b ht X := by
    funext i
    exact nativeSupportedCompensationCoefficientCLM_apply P hp v hv hb b ht i X
  refine ⟨A,B,hA,hB,?_⟩
  intro T Y
  dsimp only
  have hzero := h0 Y
  have hone := h1 (T Y)
  rw [he0] at hzero
  rw [he1] at hone
  refine ⟨MemWkp.add (by norm_num) hO hzero.1 hone.1,?_⟩
  have hTY : ENNReal.ofReal ‖T Y‖≤ENNReal.ofReal ‖T‖*ENNReal.ofReal ‖Y‖ := by
    simpa only [ENNReal.ofReal_mul (norm_nonneg T)] using ENNReal.ofReal_le_ofReal (T.le_opNorm Y)
  exact (wkpNorm_add_le (by norm_num) hO hzero.1 hone.1).trans
    ((add_le_add hzero.2 (hone.2.trans (mul_le_mul le_rfl hTY zero_le zero_le))).trans_eq (by ring))

#print axioms exists_nativeBubbleCompensation_linear_bound
#print axioms exists_nativeH4Matched_compensation_bound
end Yamabe3.Analysis.SpherePolar
