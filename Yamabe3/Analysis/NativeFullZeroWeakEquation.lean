import Yamabe3.Analysis.NativeFullModelWeakEquation
import Yamabe3.Analysis.NativeLowEntranceEquation

/-! The same full field minus its genuine finite entrance lift has a
produced global L2 equation. The source correction is explicit and the
same zero-entrance function is retained throughout. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

theorem nativeWeakEquation_smul {Ω:Set E} {P:Fin 3→E→ℝ} {g:E→ℝ}
    (c:ℝ) (he:WeakEquation Ω P g) :
    WeakEquation Ω (fun i x=>c*P i x) (fun x=>c*g x) := by
  intro φ hφ hc hs
  simp_rw [mul_assoc,←Finset.mul_sum]
  rw [integral_const_mul,integral_const_mul,he φ hφ hc hs]

variable {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)

def fullModelEntranceRHS (f:HalfEndPhysicalH2SourceGraph) : E→ℝ :=
  nativeLowEntranceRHS (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) (halfEndFullSourceAngularCLM f)

def fullModelZeroPhysicalSource (f:HalfEndPhysicalH2SourceGraph) (x:E) : ℝ :=
  halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x+
    8*(nativeHalfEndPotentialCoefficient p.potential x*fullModelEntranceLift p f x-
      fullModelEntranceRHS p f x)

def fullModelZeroNormalizedRHS (f:HalfEndPhysicalH2SourceGraph) (x:E) : ℝ :=
  fullModelZeroPhysicalSource p f x/8+
    nativeHalfEndPotentialCoefficient p.potential x*fullModelZeroEntranceField hκ0 hκ1 p f x

theorem fullModelZeroNormalizedRHS_eq (f:HalfEndPhysicalH2SourceGraph) (x:E) :
    fullModelZeroNormalizedRHS hκ0 hκ1 p f x=
      (halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8+
        nativeHalfEndPotentialCoefficient p.potential x*fullModelPhysicalField hκ0 hκ1 p f x)-
        fullModelEntranceRHS p f x := by
  have he:=fullModelPhysicalField_retained_entrance hκ0 hκ1 p f x
  unfold fullModelZeroNormalizedRHS fullModelZeroPhysicalSource
  linear_combination (nativeHalfEndPotentialCoefficient p.potential x)*he

theorem fullModelZeroEntrance_same_weak_equation (f:HalfEndPhysicalH2SourceGraph) :
    MemH01 (fullModelZeroEntranceField hκ0 hκ1 p f) O ∧
      MemLp (fullModelZeroNormalizedRHS hκ0 hκ1 p f) 2 (volume.restrict O) ∧
      ∃du:Fin 3→E→ℝ, (∀i,MemLp (du i) 2 (volume.restrict O)) ∧
        (∀i,HasWeakPartialDeriv i (du i) (fullModelZeroEntranceField hκ0 hκ1 p f) O) ∧
        WeakEquation O du (fullModelZeroNormalizedRHS hκ0 hκ1 p f) := by
  let u:=fullModelPhysicalField hκ0 hκ1 p f
  let B:=fullModelEntranceLift p f
  let g:=fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x/8+
    nativeHalfEndPotentialCoefficient p.potential x*u x
  let gB:=fullModelEntranceRHS p f
  let v:ℝ→ℝ:=fun t=>p.orbit (t+p.phase)
  have hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
  have hb:∀t,0≤v t ∧ v t≤1:=fun t=>p.bounded (t+p.phase)
  let F:=halfEndFullSourceAngularCLM f
  have hO:IsOpen O:=Metric.isOpen_ball.sdiff isClosed_singleton
  obtain ⟨hu,hg,du,hdu,hwu,he⟩:=fullModelPhysicalField_same_weak_equation hκ0 hκ1 p f
  obtain ⟨hB,hdB⟩:=nativeLowEntranceLift_H1_gradient v hv hb F
  let dB:Fin 3→E→ℝ:=fun i x=>fderiv ℝ B x (EuclideanSpace.single i 1)
  have hBg:MemLp gB 2 (volume.restrict O):=nativeLowEntranceRHS_memLp v hv hb F
  have hBC1:ContDiffOn ℝ 1 B O:=
    ((nativeLowEntranceLift_smooth v hv hb F).mono (fun x hx=>hx.2)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  let wu:MemW1pWitness 2 u O:=⟨hu.1,fun x=>WithLp.toLp 2 (fun i=>du i x),hdu,hwu⟩
  let wB:MemW1pWitness 2 B O:=⟨hB.1,fun x=>WithLp.toLp 2 (fun i=>dB i x),hdB,
    fun i=>native_hasWeakPartialDeriv_of_contDiffOn_one hO hBC1 i⟩
  let dz:Fin 3→E→ℝ:=fun i x=>du i x+(-1)*dB i x
  have hdz:∀i,MemLp (dz i) 2 (volume.restrict O):=fun i=>(hdu i).add ((hdB i).const_mul (-1))
  have huEq:(fun x=>u x+(-1)*B x)=fullModelZeroEntranceField hκ0 hκ1 p f:=by
    funext x
    have hh:=fullModelPhysicalField_retained_entrance hκ0 hκ1 p f x
    change fullModelZeroEntranceField hκ0 hκ1 p f x+B x=u x at hh
    linarith
  have hwz:∀i,HasWeakPartialDeriv i (dz i) (fullModelZeroEntranceField hκ0 hκ1 p f) O:=by
    have hh:∀i,HasWeakPartialDeriv i (dz i) (fun x=>u x+(-1)*B x) O:=(wu.add (wB.smul (-1))).isWeakGrad
    rw [huEq] at hh
    exact hh
  have heB:WeakEquation O dB gB:=nativeLowEntranceLift_weak_equation v hv hb F
  have heZ:=nativeWeakEquation_add hdu (fun i=>(hdB i).const_mul (-1)) hg (hBg.const_mul (-1)) he
    (nativeWeakEquation_smul (-1) heB)
  have hgEq:(fun x=>g x+(-1)*gB x)=fullModelZeroNormalizedRHS hκ0 hκ1 p f:=by
    funext x
    rw [fullModelZeroNormalizedRHS_eq]
    change g x+(-1)*gB x=g x-gB x
    ring
  have hgz:MemLp (fullModelZeroNormalizedRHS hκ0 hκ1 p f) 2 (volume.restrict O):=by
    rw [←hgEq]
    exact hg.add (hBg.const_mul (-1))
  refine ⟨fullModelZeroEntranceField_H01 hκ0 hκ1 p f,hgz,dz,hdz,hwz,?_⟩
  rw [hgEq] at heZ
  exact heZ

#print axioms nativeWeakEquation_smul
#print axioms fullModelZeroNormalizedRHS_eq
#print axioms fullModelZeroEntrance_same_weak_equation
end Yamabe3.Analysis.UniformElliptic
