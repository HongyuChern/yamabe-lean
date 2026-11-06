import Yamabe3.Analysis.NativeLowZeroEntranceH01
import Yamabe3.Analysis.NativeContinuousSourceSplit
import Yamabe3.Analysis.NativeHalfEndH2SourceSolver
import Yamabe3.Analysis.DelaunayPhaseData

/-! The full physical source, its same high/low model field, and the
actual entrance lifting. Subtracting that lifting produces MemH01, by
the two actual producers. The low part is retained; the source is not
assumed high. No H4 inverse or geometric correction is asserted here. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Weak
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}

def halfEndFullSourceAngularCLM : HalfEndPhysicalH2SourceGraph →L[ℝ] (ℝ →ᵇ AngularL2) :=
  (cylinderToAngularL2CLM.comp halfEndSourceCylinderCLM).comp halfEndPhysicalH2SourceGraphValue

theorem halfEndFullSourceAngular_toNNReal (f:HalfEndPhysicalH2SourceGraph) (t:ℝ) :
    halfEndFullSourceAngularCLM f t=halfEndH2SourceToAngularCLM f t.toNNReal := by
  change nativeSphereL2Inclusion ((cylinderBoundedCurry
    (halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f))) t)=
    nativeSphereL2Inclusion ((cylinderBoundedCurry
      (halfEndSourceCylinderCLM (halfEndPhysicalH2SourceGraphValue f))) (t.toNNReal:ℝ))
  congr 1
  apply ContinuousMap.ext
  intro θ
  exact (halfEndSourceCylinderCLM_toNNReal (halfEndPhysicalH2SourceGraphValue f) t θ).symm

theorem halfEndFullSourceAngular_norm_le (f:HalfEndPhysicalH2SourceGraph) :
    ‖halfEndFullSourceAngularCLM f‖≤‖nativeSphereL2Inclusion‖*‖f‖ := by
  apply (cylinderToAngularL2CLM_norm_le _).trans
  exact mul_le_mul_of_nonneg_left ((halfEndSourceCylinderCLM_norm_le _).trans (norm_fst_le f.1))
    (norm_nonneg nativeSphereL2Inclusion)

variable {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)

def fullModelHighJoint (f:HalfEndPhysicalH2SourceGraph) : ℝ × S→ℝ :=
  nativeHalfHighDirichletJoint hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
    (halfEndH2SourceToAngularCLM f)

def fullModelLowField (f:HalfEndPhysicalH2SourceGraph) : E→ℝ :=
  nativeLowPhysicalField (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) (halfEndFullSourceAngularCLM f)

def fullModelLowZeroField (f:HalfEndPhysicalH2SourceGraph) : E→ℝ :=
  nativeLowZeroEntranceField (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) (halfEndFullSourceAngularCLM f)

def fullModelEntranceLift (f:HalfEndPhysicalH2SourceGraph) : E→ℝ :=
  nativeLowEntranceLift (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) (halfEndFullSourceAngularCLM f)

def fullModelPhysicalField (f:HalfEndPhysicalH2SourceGraph) : E→ℝ :=
  fun x=>cylinderLift (fullModelHighJoint hκ0 hκ1 p f) x+fullModelLowField p f x

def fullModelZeroEntranceField (f:HalfEndPhysicalH2SourceGraph) : E→ℝ :=
  fun x=>cylinderLift (fullModelHighJoint hκ0 hκ1 p f) x+fullModelLowZeroField p f x

theorem fullModelZeroEntranceField_H01 (f:HalfEndPhysicalH2SourceGraph) :
    MemH01 (fullModelZeroEntranceField hκ0 hκ1 p f) O := by
  have hh:=native_forced_halfEnd_memH01 hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
    (halfEndH2SourceToAngularCLM f)
    (nativeHalfHighDirichletJoint_measurable hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _)
    (nativeHalfHighDirichletJoint_ae hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _)
  have hl:=nativeLowZeroEntranceField_H01 (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) (halfEndFullSourceAngularCLM f)
  exact hh.add hl

theorem fullModelPhysicalField_H1 (f:HalfEndPhysicalH2SourceGraph) :
    MemH1 (fullModelPhysicalField hκ0 hκ1 p f) O := by
  have hh:MemH1 (cylinderLift (fullModelHighJoint hκ0 hκ1 p f)) O:=
    (native_forced_halfEnd_memH01 hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
      (halfEndH2SourceToAngularCLM f)
      (nativeHalfHighDirichletJoint_measurable hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _)
      (nativeHalfHighDirichletJoint_ae hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg _)).1
  let v:ℝ→ℝ:=fun t=>p.orbit (t+p.phase)
  have hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
  have hb:∀t,0≤v t ∧ v t≤1:=fun t=>p.bounded (t+p.phase)
  let F:=halfEndFullSourceAngularCLM f
  have hl:MemH1 (fullModelLowField p f) O:=
    (finitePhysical_H1_of_exp_decay nativeLowIndexFinset (nativeLowPhysicalCoefficient v hv hb F)
      (fun i _=>(nativeLowPhysicalCoefficient_C2_equation v hv hb F i).1)
      (A:=2*‖F‖) (B:=12*‖F‖) (by positivity) (by positivity)
      (fun i _ t _=>(nativeLowPhysicalCoefficient_bounds v hv hb F i t).1)
      (fun i _ t _=>(nativeLowPhysicalCoefficient_bounds v hv hb F i t).2)).1
  exact (hh.someWitness.add hl.someWitness).memW1p

theorem fullModelPhysicalField_retained_entrance (f:HalfEndPhysicalH2SourceGraph) (x:E) :
    fullModelZeroEntranceField hκ0 hκ1 p f x+fullModelEntranceLift p f x=
      fullModelPhysicalField hκ0 hκ1 p f x := by
  have he:=nativeLowPhysicalField_split_entrance (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) (halfEndFullSourceAngularCLM f) x
  change fullModelLowZeroField p f x+fullModelEntranceLift p f x=fullModelLowField p f x at he
  change (_+fullModelLowZeroField p f x)+fullModelEntranceLift p f x=_+fullModelLowField p f x
  rw [add_assoc,he]

#print axioms halfEndFullSourceAngular_toNNReal
#print axioms halfEndFullSourceAngular_norm_le
#print axioms fullModelZeroEntranceField_H01
#print axioms fullModelPhysicalField_H1
#print axioms fullModelPhysicalField_retained_entrance
end Yamabe3.Analysis.UniformElliptic
