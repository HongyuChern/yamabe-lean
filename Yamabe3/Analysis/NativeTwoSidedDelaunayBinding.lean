import Yamabe3.Analysis.NativeTwoSidedGlobalPhysicalEquation
import Yamabe3.Analysis.NativePhysicalWeakAssembly

/-! Identification of the same two-source all-scale row with the actual
Delaunay native weak operator. The potential equality, density and
scaling are proved, not supplied as interface assumptions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean

theorem nativeBCFCollarError_delaunay_eq (g : RiemannianMetric 3 E) (r : ℝ)
    (v : ℝ→ℝ) (hv : ContDiff ℝ ∞ v) (hb : ∀t,0≤v t ∧ v t≤1) (phase : ℝ) :
    nativeBCFCollarErrorCLM g r (delaunayPhasePotentialBCF v hv.continuous hb phase)=
      nativeFullCollarJetErrorCLM g r v hv phase := by
  let V := delaunayPhasePotentialBCF v hv.continuous hb phase
  have hQ (x : E) : nativeHalfEndPotentialCoefficient V x= -annularDelaunayPotential v phase x := by
    change (15/4)*v (-Real.log ‖x‖+phase)^4/‖x‖^2= -(-(15/4)*v (phase-Real.log ‖x‖)^4/‖x‖^2)
    rw [show -Real.log ‖x‖+phase=phase-Real.log ‖x‖ by ring]
    ring
  have he : nativeBCFPotentialError g r V=nativeDelaunayPotentialError g r v phase := by
    funext x
    simp only [nativeBCFPotentialError,nativeDelaunayPotentialError,hQ]
    ring
  apply ContinuousLinearMap.ext
  intro J
  change -nativeCollarGeometricErrorCLM g r J+
    nativeCollarLocalMulCLM (nativeBCFPotentialError g r V) (nativeBCFPotentialError_continuousOn g r V) J.1=
    -nativeCollarGeometricErrorCLM g r J+nativeCollarPotentialErrorCLM g r v hv phase J.1
  apply congrArg (fun U : NativeCollarL2 => -nativeCollarGeometricErrorCLM g r J+U)
  apply Lp.ext
  filter_upwards [nativeCollarLocalMulCLM_ae (nativeBCFPotentialError g r V)
    (nativeBCFPotentialError_continuousOn g r V) J.1,nativeCollarPotentialErrorCLM_ae g r v hv phase J.1]
    with x hx hy
  rw [hx,hy,he]

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (p : DelaunayPhaseData κ)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ) (t₀ : ℝ)
local notation "P" => p.nativeHighPotential hκ0 hκ1
local notation "v" => (fun t => p.orbit (t+p.phase))
local notation "hv" => (p.smooth.continuous.comp (continuous_id.add continuous_const))
local notation "hb" => (fun t => p.bounded (t+p.phase))

theorem nativeTwoSidedDelaunay_row (g : RiemannianMetric 3 E) (ε s : ℝ) (X : NativeTwoSidedSource) :
    nativeTwoSidedJacobianRowCLM P hp v hv hb t₀ g ε s X=
      nativeOrbitCollarJacobianCLM g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s)
        (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X) := by
  change nativeFlatCollarJetCLM (boundedTimeTranslate ℝ s p.potential)
      (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X)+
    nativeBCFCollarErrorCLM g (ε*Real.exp (-s)) (boundedTimeTranslate ℝ s p.potential)
      (nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X)=_
  rw [delaunayPhasePotential_time_translate,nativeBCFCollarError_delaunay_eq]
  rfl

theorem nativeTwoSidedDelaunay_physical_row (g : RiemannianMetric 3 E) (ε : ℝ)
    (X : NativeTwoSidedSource) {u : E→ℝ} (s : ℝ)
    (he : ((nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))) :
    (fun x => Real.exp (s/2)*(nativeTwoSidedJacobianRowCLM P hp v hv hb t₀ g ε s X : E→ℝ) (Real.exp s • x))
      =ᵐ[volume.restrict (nativePhysicalScaleWindow s)]
        nativeWeakRescaledDelaunayJacobian (nativePhysicalScaleWindow s) g ε p.orbit p.phase u := by
  rw [nativeTwoSidedDelaunay_row]
  let J := nativeTwoSidedAllScaleJetCLM P hp v hv hb t₀ s X
  have hweak := nativeOrbitCollarJacobian_weak_ae g (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s) J
  have hcongr := nativeWeakRescaledDelaunayJacobian_congr (nativePolarTimeWindow_open (1/2)) g (ε*Real.exp (-s)) p.orbit (p.phase+s) he
  have hc := ae_comp_dilation (Real.exp_ne_zero s) (hweak.trans hcongr)
  have hu := (MemWkp_congr_ae (by norm_num) (nativePolarTimeWindow_open (1/2)) he).mp
    (nativeTwoSidedAllScale_memH2 P hp v hv hb t₀ s X)
  have hphys := nativeWeakPhysicalRow_identity g ε p.orbit p.phase s hu
  filter_upwards [hc,hphys] with x hc hp
  exact (congrArg (fun z : ℝ => Real.exp (s/2)*z) hc).trans hp

theorem nativeTwoSidedDelaunay_physical_operator (g : RiemannianMetric 3 E) (ε : ℝ)
    (X : NativeTwoSidedSource) {u : E→ℝ}
    (he : ∀s : ℝ,((nativeTwoSidedAllScaleRawJetCLM P hp v hv hb t₀ s X).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      (fun x => Real.exp (3*s/2)*u (Real.exp (-s) • x))) :
    nativeTwoSidedPhysicalJacobian P hp v hv hb t₀ g ε X=ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})]
      nativePhysicalWeakJacobian g ε p.orbit p.phase u := by
  rw [←nativePhysicalShell_union,ae_eq_restrict_iUnion_iff]
  intro n
  have h := nativeTwoSidedDelaunay_physical_row hκ0 hκ1 p hp t₀ g ε X (nativeLogShellCenter n) (he _)
  have hh := ae_mono (Measure.restrict_mono (nativePhysicalShell_subset_window n) le_rfl) h
  filter_upwards [hh,ae_restrict_mem (nativePhysicalShell_measurable n)] with x hh hx
  rw [nativePhysicalWeakJacobian_on g ε p.orbit p.phase u n hx]
  change nativePhysicalShellAssembly _ x=_
  rw [nativePhysicalShellAssembly_on _ n hx]
  exact hh

#print axioms nativeBCFCollarError_delaunay_eq
#print axioms nativeTwoSidedDelaunay_row
#print axioms nativeTwoSidedDelaunay_physical_row
#print axioms nativeTwoSidedDelaunay_physical_operator
end Yamabe3.Analysis.SpherePolar
