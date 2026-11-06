import Yamabe3.Analysis.NativeShellEquationReturn
import Yamabe3.Analysis.NativeGlobalSourceFeedback

/-! Same-field model Jacobian plus the actual geometric error, assembled
in high-source pairing. Identifying the model potential with the chosen
orbit is a separate explicit obligation. Low residuals are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
attribute [local irreducible] nativeL2HalfGeometricRowCLM nativeShellSourceReturnCLM nativeGeometricSourceTerm

private theorem operator_inner_hasSum {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (T : ℕ → X →L[ℝ] X) (hs : Summable T) (F G : X) :
    HasSum (fun n => inner ℝ (T n F) G) (inner ℝ ((∑' n,T n) F) G) := by
  let ev := ContinuousLinearMap.apply ℝ X F
  have h : HasSum (fun n => inner ℝ G (T n F)) (inner ℝ G ((∑' n,T n) F)) :=
    (hs.hasSum.mapL ev).mapL (innerSL ℝ G)
  simpa only [real_inner_comm] using h

variable (P : NativeHighPotential)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)

def nativeHalfModelJacobianRowCLM (s : ℝ) : NativeSpectralSourceL2 →L[ℝ] NativeCollarL2 :=
  -((∑ j : Fin 3,nativeL2HalfAllScaleSecondCLM P hp s j j)+
    (nativeCollarPotentialMulCLM (boundedTimeTranslate ℝ s P.potential)).comp
      (nativeL2HalfAllScaleValueCLM P hp s))

def nativeHalfGeometricJacobianRowCLM (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase s : ℝ) : NativeSpectralSourceL2 →L[ℝ] NativeCollarL2 :=
  nativeHalfModelJacobianRowCLM P hp s+nativeL2HalfGeometricRowCLM P hp g ε v hv phase s

theorem nativeHalfGeometricJacobianRow_return (g : RiemannianMetric 3 E) (ε : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (phase : ℝ) (n : ℕ) (F : NativeSpectralSourceL2) :
    nativeShellSourceReturnCLM (nativeLogShellCenter n)
      (nativeHalfGeometricJacobianRowCLM P hp g ε v hv phase (nativeLogShellCenter n) F)=
      -nativeShellSourceReturnCLM (nativeLogShellCenter n)
        (nativeL2HighPhysicalSourceCLM (l2TimeTranslateCLM (SpectralSpace AngularIndex) (nativeLogShellCenter n) F))+
          nativeGeometricSourceTerm P hp g ε v hv phase n F := by
  simp only [nativeHalfGeometricJacobianRowCLM,nativeHalfModelJacobianRowCLM,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,nativeGeometricSourceTerm]
  rw [map_add,map_neg,nativeHalfEquation_shell_return]

theorem nativeGlobalGeometricSource_pairing_hasSum
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p∈Λ,(g p).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (p : ι) (hpΛ : p∈Λ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (hvb : ∀ t,0≤v t ∧ v t≤1 ∧ |deriv v t|≤1/2)
    (hvo : ∀ t,deriv (deriv v) t=radialForce (v t)) (phase : ℝ)
    (F G : NativeSpectralSourceL2) :
    HasSum (fun n => inner ℝ (nativeGeometricSourceTerm P hp (g p) ε v hv phase n F) G)
      (inner ℝ (nativeGlobalGeometricSourceCLM P hp (g p) ε v hv phase F) G) := by
  have hs := nativeGeometricSourceTerm_summable P hp Λ g hB hρ ε hε hε1 p hpΛ v hv hvb hvo phase
  exact operator_inner_hasSum _ hs F G


theorem nativeGlobalGeometricJacobian_pairing
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ p∈Λ,(g p).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (p : ι) (hpΛ : p∈Λ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (hvb : ∀ t,0≤v t ∧ v t≤1 ∧ |deriv v t|≤1/2)
    (hvo : ∀ t,deriv (deriv v) t=radialForce (v t)) (phase : ℝ)
    (F G : NativeSpectralSourceL2) :
    HasSum (fun n => inner ℝ
      (nativeShellSourceReturnCLM (nativeLogShellCenter n)
        (nativeHalfGeometricJacobianRowCLM P hp (g p) ε v hv phase (nativeLogShellCenter n) F)) G)
      (-(∫ t in Ioi 0,nativeHighSourcePairing F G t)+
        inner ℝ (nativeGlobalGeometricSourceCLM P hp (g p) ε v hv phase F) G) := by
  have h1 := (nativeHighSourceReturn_reconstructs F G).neg
  have h2 := nativeGlobalGeometricSource_pairing_hasSum P hp Λ g hB hρ ε hε hε1 p hpΛ v hv hvb hvo phase F G
  simpa only [nativeHalfGeometricJacobianRow_return,inner_add_left,inner_neg_left] using h1.add h2

#print axioms nativeHalfGeometricJacobianRow_return
#print axioms nativeGlobalGeometricSource_pairing_hasSum
#print axioms nativeGlobalGeometricJacobian_pairing
end Yamabe3.Analysis.SpherePolar
