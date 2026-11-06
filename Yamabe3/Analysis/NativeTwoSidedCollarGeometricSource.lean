import Yamabe3.Analysis.NativeTwoSidedSourceMatching
import Yamabe3.Analysis.NativeFullCollarSourceReconstruction
import Yamabe3.Analysis.NativeExteriorGeometricResidualBound

/-! The actual geometric errors of the matched two-sided jets are
returned to the same pair of source spaces by the proved physical right
inverse. This is an explicit small operator, before its feedback is solved. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v : ℝ→ℝ) (hv : Continuous v) (hb : ∀t,0≤v t ∧ v t≤1)
  {t₀ : ℝ} (ht : 0<t₀)

def nativeTwoSidedInteriorErrorCLM (g : RiemannianMetric 3 E) (r : ℝ) : NativeTwoSidedSource →L[ℝ] NativeCollarL2 :=
  (nativeBCFCollarErrorCLM g r P.potential).comp
    (nativeCollarJetClosure.subtypeL.comp (nativeTwoSidedInteriorJetCLM P hp v hv hb t₀))

def nativeTwoSidedExteriorErrorCLM (g : RiemannianMetric 3 E) (r : ℝ) : NativeTwoSidedSource →L[ℝ] NativeCollarL2 :=
  (nativeBCFCollarErrorCLM g r (nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀)))).comp
    (nativeCollarJetClosure.subtypeL.comp (nativeTwoSidedExteriorJetCLM P hp v hv hb ht))

def nativeTwoSidedCollarSourceErrorCLM (g : RiemannianMetric 3 E) (r : ℝ) : NativeTwoSidedSource →L[ℝ] NativeTwoSidedSource :=
  (nativeFullCollarSourceReturnCLM.comp (nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) g r)).prod
    (nativeFullCollarSourceReturnCLM.comp (nativeTwoSidedExteriorErrorCLM P hp v hv hb ht g r))

theorem nativeTwoSidedCollarSourceError_reconstructs (g : RiemannianMetric 3 E) (r : ℝ) (X : NativeTwoSidedSource) :
    nativeL2FullPhysicalSourceCLM (nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r X).1=
      nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) g r X ∧
    nativeL2FullPhysicalSourceCLM (nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht g r X).2=
      nativeTwoSidedExteriorErrorCLM P hp v hv hb ht g r X :=
  ⟨nativeFullCollarSourceReturn_right_inverse _,nativeFullCollarSourceReturn_right_inverse _⟩

theorem exists_nativeTwoSidedCollarSourceError_linear_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0≤r → r≤1 → ∀p∈Λ,
      ‖nativeTwoSidedCollarSourceErrorCLM P hp v hv hb ht (g p) r‖≤C*r := by
  let V := nativePoissonExteriorPotential (fullBubbleHighPotential (-t₀))
  let M := max ‖P.potential‖ ‖V‖
  have hM : 0≤M := (norm_nonneg P.potential).trans (le_max_left _ _)
  obtain ⟨C,hC,hc⟩ := exists_native_bcf_full_collar_error_linear_bound Λ g hB hρ hM
  let J := nativeTwoSidedInteriorJetCLM P hp v hv hb t₀
  let K := nativeTwoSidedExteriorJetCLM P hp v hv hb ht
  let A := nativeFullCollarSourceReturnCLM
  let D := 1+‖A‖*C*(‖J‖+‖K‖)
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨D,hD,fun r hr hr1 p hp' => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hD.le hr)
  intro X
  have hJ := hc r hr hr1 p hp' P.potential (le_max_left _ _) (J X).val
  have hK := hc r hr hr1 p hp' V (le_max_right _ _) (K X).val
  have haJ := A.le_opNorm (nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) (g p) r X)
  have haK := A.le_opNorm (nativeTwoSidedExteriorErrorCLM P hp v hv hb ht (g p) r X)
  change ‖nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) (g p) r X‖≤(C*r)*‖J X‖ at hJ
  change ‖nativeTwoSidedExteriorErrorCLM P hp v hv hb ht (g p) r X‖≤(C*r)*‖K X‖ at hK
  have hJJ := J.le_opNorm X
  have hKK := K.le_opNorm X
  have hleft : ‖A (nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) (g p) r X)‖≤(D*r)*‖X‖ := by
    apply haJ.trans
    apply (mul_le_mul_of_nonneg_left hJ (norm_nonneg A)).trans
    rw [←mul_assoc]
    apply (mul_le_mul_of_nonneg_left hJJ (by positivity : 0≤‖A‖*(C*r))).trans
    dsimp only [D]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg A) hC.le) (norm_nonneg K))
      (mul_nonneg hr (norm_nonneg X)),mul_nonneg hr (norm_nonneg X)]
  have hright : ‖A (nativeTwoSidedExteriorErrorCLM P hp v hv hb ht (g p) r X)‖≤(D*r)*‖X‖ := by
    apply haK.trans
    apply (mul_le_mul_of_nonneg_left hK (norm_nonneg A)).trans
    rw [←mul_assoc]
    apply (mul_le_mul_of_nonneg_left hKK (by positivity : 0≤‖A‖*(C*r))).trans
    dsimp only [D]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg A) hC.le) (norm_nonneg J))
      (mul_nonneg hr (norm_nonneg X)),mul_nonneg hr (norm_nonneg X)]
  change ‖(A (nativeTwoSidedInteriorErrorCLM P hp v hv hb (t₀:=t₀) (g p) r X),
    A (nativeTwoSidedExteriorErrorCLM P hp v hv hb ht (g p) r X))‖≤_
  rw [Prod.norm_def]
  exact max_le hleft hright

#print axioms nativeTwoSidedCollarSourceError_reconstructs
#print axioms exists_nativeTwoSidedCollarSourceError_linear_bound
end Yamabe3.Analysis.SpherePolar
