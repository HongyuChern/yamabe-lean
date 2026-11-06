import Yamabe3.Analysis.NativeLowFieldLinearity

/-! The completion and the actual finite lifting are source-linear in
their correct senses: volume-a.e. for the L2 representative, pointwise
for the explicitly constructed finite lifting. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}
variable {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (p:DelaunayPhaseData κ)

def fullModelHighPhysicalL2CLM : HalfEndPhysicalH2SourceGraph→L[ℝ] Lp ℝ 2 (volume.restrict O) :=
  (nativeHalfHighDirichletPhysicalCLM hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg).comp
    halfEndH2SourceToAngularCLM

theorem fullModelHighPhysicalL2CLM_rep (f:HalfEndPhysicalH2SourceGraph) :
    (fullModelHighPhysicalL2CLM hκ0 hκ1 p f:E→ℝ) =ᵐ[volume.restrict O]
      cylinderLift (fullModelHighJoint hκ0 hκ1 p f) :=
  (nativeHalfHighDirichletJoint_lift_memLp hκ0 hκ1 p.potential p.kernel_bound p.potential_nonneg
    (halfEndH2SourceToAngularCLM f)).coeFn_toLp

theorem fullModelZeroEntranceField_add_ae (f g:HalfEndPhysicalH2SourceGraph) :
    fullModelZeroEntranceField hκ0 hκ1 p (f+g) =ᵐ[volume.restrict O]
      fullModelZeroEntranceField hκ0 hκ1 p f+fullModelZeroEntranceField hκ0 hκ1 p g := by
  let C:=fullModelHighPhysicalL2CLM hκ0 hκ1 p
  have hC:(C (f+g):E→ℝ) =ᵐ[volume.restrict O] (C f:E→ℝ)+(C g:E→ℝ):=by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have hL:fullModelLowZeroField p (f+g)=fullModelLowZeroField p f+fullModelLowZeroField p g:=by
    unfold fullModelLowZeroField
    rw [map_add,nativeLowZeroEntranceField_add]
  filter_upwards [hC,fullModelHighPhysicalL2CLM_rep hκ0 hκ1 p (f+g),
    fullModelHighPhysicalL2CLM_rep hκ0 hκ1 p f,fullModelHighPhysicalL2CLM_rep hκ0 hκ1 p g] with x hC hfg hf hg
  simp only [Pi.add_apply] at hC
  rw [hfg,hf,hg] at hC
  change cylinderLift (fullModelHighJoint hκ0 hκ1 p (f+g)) x+fullModelLowZeroField p (f+g) x=
    (cylinderLift (fullModelHighJoint hκ0 hκ1 p f) x+fullModelLowZeroField p f x)+
    (cylinderLift (fullModelHighJoint hκ0 hκ1 p g) x+fullModelLowZeroField p g x)
  rw [hC,hL,Pi.add_apply]
  ring

theorem fullModelZeroEntranceField_smul_ae (c:ℝ) (f:HalfEndPhysicalH2SourceGraph) :
    fullModelZeroEntranceField hκ0 hκ1 p (c • f) =ᵐ[volume.restrict O]
      c • fullModelZeroEntranceField hκ0 hκ1 p f := by
  let C:=fullModelHighPhysicalL2CLM hκ0 hκ1 p
  have hC:(C (c • f):E→ℝ) =ᵐ[volume.restrict O] c • (C f:E→ℝ):=by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  have hL:fullModelLowZeroField p (c • f)=c • fullModelLowZeroField p f:=by
    unfold fullModelLowZeroField
    rw [map_smul,nativeLowZeroEntranceField_smul]
  filter_upwards [hC,fullModelHighPhysicalL2CLM_rep hκ0 hκ1 p (c • f),
    fullModelHighPhysicalL2CLM_rep hκ0 hκ1 p f] with x hC hcf hf
  simp only [Pi.smul_apply,smul_eq_mul] at hC
  rw [hcf,hf] at hC
  change cylinderLift (fullModelHighJoint hκ0 hκ1 p (c • f)) x+fullModelLowZeroField p (c • f) x=
    c*(cylinderLift (fullModelHighJoint hκ0 hκ1 p f) x+fullModelLowZeroField p f x)
  rw [hC,hL,Pi.smul_apply,smul_eq_mul]
  ring

theorem fullModelCompletionPair_add_ae (f g:HalfEndPhysicalH2SourceGraph) :
    (fullModelCompletionPair hκ0 hκ1 p (f+g)).1 =ᵐ[volume]
      (fullModelCompletionPair hκ0 hκ1 p f).1+(fullModelCompletionPair hκ0 hκ1 p g).1 ∧
    (fullModelCompletionPair hκ0 hκ1 p (f+g)).2=
      (fullModelCompletionPair hκ0 hκ1 p f).2+(fullModelCompletionPair hκ0 hκ1 p g).2 := by
  constructor
  · have hu:=(ae_restrict_iff' (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet).mp
      (fullModelZeroEntranceField_add_ae hκ0 hκ1 p f g)
    filter_upwards [fullModelZeroCompletion_rep hκ0 hκ1 p (f+g),fullModelZeroCompletion_rep hκ0 hκ1 p f,
      fullModelZeroCompletion_rep hκ0 hκ1 p g,hu] with x hfg hf hg hu
    change toL2 nativeWeakEuclideanD O (fullModelZeroCompletion hκ0 hκ1 p (f+g)) x=
      toL2 nativeWeakEuclideanD O (fullModelZeroCompletion hκ0 hκ1 p f) x+
      toL2 nativeWeakEuclideanD O (fullModelZeroCompletion hκ0 hκ1 p g) x
    rw [hfg,hf,hg]
    by_cases hx:x∈O
    · simpa only [indicator_of_mem hx,Pi.add_apply] using hu hx
    · simp only [indicator_of_notMem hx,zero_add]
  · change fullModelEntranceLift p (f+g)=fullModelEntranceLift p f+fullModelEntranceLift p g
    unfold fullModelEntranceLift
    rw [map_add,nativeLowEntranceLift_add]

theorem fullModelCompletionPair_smul_ae (c:ℝ) (f:HalfEndPhysicalH2SourceGraph) :
    (fullModelCompletionPair hκ0 hκ1 p (c • f)).1 =ᵐ[volume]
      c • (fullModelCompletionPair hκ0 hκ1 p f).1 ∧
    (fullModelCompletionPair hκ0 hκ1 p (c • f)).2=c • (fullModelCompletionPair hκ0 hκ1 p f).2 := by
  constructor
  · have hu:=(ae_restrict_iff' (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet).mp
      (fullModelZeroEntranceField_smul_ae hκ0 hκ1 p c f)
    filter_upwards [fullModelZeroCompletion_rep hκ0 hκ1 p (c • f),
      fullModelZeroCompletion_rep hκ0 hκ1 p f,hu] with x hcf hf hu
    change toL2 nativeWeakEuclideanD O (fullModelZeroCompletion hκ0 hκ1 p (c • f)) x=
      c*toL2 nativeWeakEuclideanD O (fullModelZeroCompletion hκ0 hκ1 p f) x
    rw [hcf,hf]
    by_cases hx:x∈O
    · simpa only [indicator_of_mem hx,Pi.smul_apply,smul_eq_mul] using hu hx
    · simp only [indicator_of_notMem hx,mul_zero]
  · change fullModelEntranceLift p (c • f)=c • fullModelEntranceLift p f
    unfold fullModelEntranceLift
    rw [map_smul,nativeLowEntranceLift_smul]

#print axioms fullModelHighPhysicalL2CLM_rep
#print axioms fullModelZeroEntranceField_add_ae
#print axioms fullModelZeroEntranceField_smul_ae
#print axioms fullModelCompletionPair_add_ae
#print axioms fullModelCompletionPair_smul_ae
end Yamabe3.Analysis.UniformElliptic
