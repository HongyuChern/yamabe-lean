import Yamabe3.Analysis.NativeH4GraphSphereTrace
import Yamabe3.Analysis.NativeSpectralJetMatching

/-! The high boundary correction is an actual linear producer on the
original H4 graph. It uses the literal value/radial derivative and the
already constructed same-high-space coupled inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay

private theorem high_idem (f : AngularL2) : nativeHighProjection (nativeHighProjection f)=nativeHighProjection f := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply,nativeHighProjection,nativeAngularProjection_coefficient]
  split_ifs <;> rfl

def nativeH4GraphHighValue (v : HalfEndPhysicalH4Graph) : AngularH1 :=
  Classical.choose (nativeAngular_three_halves_exists_H1 _
    (nativeAngularSpectralRegular_high (nativeH4Graph_actual_trace_spectral v).1).1)

theorem nativeH4GraphHighValue_embedding (v : HalfEndPhysicalH4Graph) :
    angularEmbedding (nativeH4GraphHighValue v)=nativeHighProjection (nativeH4GraphAngularValueCLM v) :=
  (Classical.choose_spec (nativeAngular_three_halves_exists_H1 _
    (nativeAngularSpectralRegular_high (nativeH4Graph_actual_trace_spectral v).1).1)).1

def nativeH4GraphHighValueLinear : HalfEndPhysicalH4Graph →ₗ[ℝ] AngularH1 where
  toFun := nativeH4GraphHighValue
  map_add' v w := by
    apply angularEmbedding_injective
    simp only [map_add,nativeH4GraphHighValue_embedding]
  map_smul' c v := by
    apply angularEmbedding_injective
    simp only [map_smul,nativeH4GraphHighValue_embedding,RingHom.id_apply]

def nativeH4GraphHighValueCLM : HalfEndPhysicalH4Graph →L[ℝ] AngularH1 :=
  ⟨nativeH4GraphHighValueLinear,by
    apply nativeH4GraphHighValueLinear.continuous_of_seq_closed_graph
    intro u x y hu hy
    apply angularEmbedding_injective
    have h1 := angularEmbedding.continuous.tendsto y |>.comp hy
    have h2 := (nativeHighProjection.comp nativeH4GraphAngularValueCLM).continuous.tendsto x |>.comp hu
    have he : (fun n => angularEmbedding (nativeH4GraphHighValueLinear (u n)))=
      (fun n => nativeHighProjection (nativeH4GraphAngularValueCLM (u n))) :=
      funext (fun n => nativeH4GraphHighValue_embedding (u n))
    change Tendsto (fun n => angularEmbedding (nativeH4GraphHighValueLinear (u n))) _ _ at h1
    rw [he] at h1
    exact (tendsto_nhds_unique h1 h2).trans (nativeH4GraphHighValue_embedding x).symm⟩

theorem nativeH4GraphHighValue_high (v : HalfEndPhysicalH4Graph) :
    nativeHighEnergyProjectionCLM (nativeH4GraphHighValueCLM v)=nativeH4GraphHighValueCLM v := by
  apply angularEmbedding_injective
  rw [nativeHighEnergyProjectionCLM_embedding]
  change nativeHighProjection (angularEmbedding (nativeH4GraphHighValue v))=angularEmbedding (nativeH4GraphHighValue v)
  rw [nativeH4GraphHighValue_embedding,high_idem]

theorem nativeH4GraphHighValue_regular (v : HalfEndPhysicalH4Graph) :
    NativeAngularSpectralRegular (3/2) (angularEmbedding (nativeH4GraphHighValueCLM v)) := by
  change NativeAngularSpectralRegular (3/2) (angularEmbedding (nativeH4GraphHighValue v))
  rw [nativeH4GraphHighValue_embedding]
  exact (nativeAngularSpectralRegular_high (nativeH4Graph_actual_trace_spectral v).1).1

def nativeH4GraphNormalJumpCLM : HalfEndPhysicalH4Graph →L[ℝ] AngularL2 :=
  -(nativeHighProjection.comp nativeH4GraphAngularNormalCLM)-(1/2:ℝ) • (angularEmbedding.comp nativeH4GraphHighValueCLM)

theorem nativeH4GraphNormalJump_high (v : HalfEndPhysicalH4Graph) :
    nativeHighProjection (nativeH4GraphNormalJumpCLM v)=nativeH4GraphNormalJumpCLM v := by
  change nativeHighProjection (-nativeHighProjection (nativeH4GraphAngularNormalCLM v)-
    (1/2:ℝ) • angularEmbedding (nativeH4GraphHighValue v))=_
  rw [map_sub,map_neg,map_smul,nativeH4GraphHighValue_embedding,high_idem,high_idem]
  change _= -nativeHighProjection (nativeH4GraphAngularNormalCLM v)-(1/2:ℝ) • angularEmbedding (nativeH4GraphHighValue v)
  rw [nativeH4GraphHighValue_embedding]

theorem nativeH4GraphNormalJump_regular (v : HalfEndPhysicalH4Graph) :
    NativeAngularSpectralRegular (1/2) (nativeH4GraphNormalJumpCLM v) := by
  change NativeAngularSpectralRegular (1/2) (-nativeHighProjection (nativeH4GraphAngularNormalCLM v)-
    (1/2:ℝ) • angularEmbedding (nativeH4GraphHighValueCLM v))
  exact (nativeAngularSpectralRegular_sub
    (by simpa only [neg_one_smul] using (nativeAngularSpectralRegular_smul
      (nativeAngularSpectralRegular_high (nativeH4Graph_actual_trace_spectral v).2).1 (-1)).1)
    (nativeAngularSpectralRegular_smul
      (nativeAngular_three_halves_to_half _ (nativeH4GraphHighValue_regular v)).1 (1/2)).1).1

def nativeH4GraphSigmaCLM (B P : NativeHighPotential) : HalfEndPhysicalH4Graph →L[ℝ] AngularH1 :=
  (nativeHighCoupledDtNInverse B P).comp (nativeH4GraphNormalJumpCLM-B.dtn.comp nativeH4GraphHighValueCLM)

theorem nativeH4GraphSigma_high (B P : NativeHighPotential) (v : HalfEndPhysicalH4Graph) :
    nativeHighEnergyProjectionCLM (nativeH4GraphSigmaCLM B P v)=nativeH4GraphSigmaCLM B P v :=
  nativeHighCoupledDtNInverse_high _ _ _

theorem nativeH4GraphSigma_equation (B P : NativeHighPotential) (v : HalfEndPhysicalH4Graph) :
    B.dtn (nativeH4GraphSigmaCLM B P v+nativeH4GraphHighValueCLM v)+P.dtn (nativeH4GraphSigmaCLM B P v)=
      nativeH4GraphNormalJumpCLM v := by
  have h := nativeHighCoupledDtNInverse_right B P
    (nativeH4GraphNormalJumpCLM v-B.dtn (nativeH4GraphHighValueCLM v))
  rw [nativeHighProjection.map_sub,nativeH4GraphNormalJump_high,B.high] at h
  change B.dtn (nativeH4GraphSigmaCLM B P v)+P.dtn (nativeH4GraphSigmaCLM B P v)=_ at h
  rw [map_add]
  calc
    _=(B.dtn (nativeH4GraphSigmaCLM B P v)+P.dtn (nativeH4GraphSigmaCLM B P v))+B.dtn (nativeH4GraphHighValueCLM v) := by abel
    _=_ := by rw [h];abel

theorem nativeH4GraphSigma_regular (B P : NativeHighPotential) (v : HalfEndPhysicalH4Graph) :
    NativeAngularSpectralRegular (3/2) (angularEmbedding (nativeH4GraphSigmaCLM B P v)) := by
  have h := (nativeHighCoupled_cauchy_spectral_regular B P (nativeH4GraphHighValueCLM v)
    (nativeH4GraphNormalJumpCLM v) (1/2)
    (by convert nativeH4GraphHighValue_regular v using 1 <;> norm_num)
    (nativeH4GraphNormalJump_regular v)).1
  convert h using 1 <;> norm_num [nativeH4GraphSigmaCLM,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply]

#print axioms nativeH4GraphHighValue_embedding
#print axioms nativeH4GraphHighValueCLM
#print axioms nativeH4GraphHighValue_high
#print axioms nativeH4GraphHighValue_regular
#print axioms nativeH4GraphNormalJump_regular
#print axioms nativeH4GraphSigma_equation
#print axioms nativeH4GraphSigma_regular
end Yamabe3.Analysis.UniformElliptic
