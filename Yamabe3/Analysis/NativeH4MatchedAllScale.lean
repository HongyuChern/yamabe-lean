import Yamabe3.Analysis.NativeH4GraphAllScaleJet
import Yamabe3.Analysis.NativeH4GraphCouplingBounds

/-! Actual scale jets of the original H4 field plus its uniquely coupled
Poisson correction. The same correction is used on every scale; the
uniform bound is proved from the graph norm and the spectral energy bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable (B P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)

theorem nativeH4GraphSigma_energy_bound :
    ∃D : ℝ,0≤D ∧ ∀v,nativePoissonBoundaryEnergy (nativeH4GraphSigmaCLM B P v)≤D*‖v‖^2 := by
  obtain ⟨D,hD,h⟩ := exists_nativeH4Graph_coupling_energy_bound B
  exact ⟨D,hD,fun v => (h P v).1⟩

def nativeH4MatchedScaleJetCLM (i : HalfEndPhysicalSliceIndex) : HalfEndPhysicalH4Graph →L[ℝ] nativeCollarJetClosure :=
  nativeH4GraphScaleJetCLM i+
    nativeBoundaryPoissonJetCLM P hp (nativeH4GraphSigmaCLM B P)
      (nativeH4GraphSigma_regular B P) (nativeH4GraphSigma_energy_bound B P) i.1

def nativeH4MatchedScaleRawJetCLM (i : HalfEndPhysicalSliceIndex) : HalfEndPhysicalH4Graph →L[ℝ] NativeCollarJet :=
  nativeCollarJetClosure.subtypeL.comp (nativeH4MatchedScaleJetCLM B P hp i)

theorem nativeH4MatchedScale_memH2 (i : HalfEndPhysicalSliceIndex) (v : HalfEndPhysicalH4Graph) :
    MemWkp 2 2 (nativeH4MatchedScaleRawJetCLM B P hp i v).1 nativePoissonEntranceCollar :=
  nativeCollarJetClosure_memH2 (nativeH4MatchedScaleJetCLM B P hp i v)

theorem nativeH4MatchedScale_same_field (v : HalfEndPhysicalH4Graph) (F : E→ℝ)
    (hF : EqOn (halfEndEntranceExtension (halfEndPhysicalH4GraphValue v)) F (closedBall (0:E) 4)) :
    ∃q : ℝ×S→ℝ,Measurable q ∧
      (∀t,(fun θ => q (t,θ))=ᵐ[angularVolume] (nativePoissonReflectedCurve P (nativeH4GraphSigmaCLM B P v) t : S→ℝ)) ∧
      ∀i : HalfEndPhysicalSliceIndex,
        ((nativeH4MatchedScaleRawJetCLM B P hp i v).1 : E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
          (fun x => Real.exp (3*i.1/2)*(F (Real.exp (-i.1) • x)+cylinderLift q (Real.exp (-i.1) • x))) := by
  let b := nativeH4GraphSigmaCLM B P v
  obtain ⟨q,hq,hqa,_⟩ := nativePoissonReflectedCurve_joint_representative P b
  refine ⟨q,hq.measurable,?_,fun i => ?_⟩
  · exact hqa
  · have hf := nativeH4GraphScaleJet_same_function i v F hF
    have hl := nativePoissonAllScaleValue_same_field P hp b (nativeH4GraphSigma_regular B P v) hq.measurable hqa i.1
    have ha := Lp.coeFn_add (nativeH4GraphScaleJetCLM i v).val.1 (nativePoissonAllScaleValue P hp i.1 b)
    filter_upwards [hf,hl,ha] with x hf hl ha
    change ((nativeH4GraphScaleJetCLM i v).val.1+nativePoissonAllScaleValue P hp i.1 b) x=_
    rw [ha]
    change (nativeH4GraphScaleJetCLM i v).val.1 x+nativePoissonAllScaleValue P hp i.1 b x=_
    rw [hf,hl,mul_add]

theorem exists_nativeH4MatchedScale_bound :
    ∃D : ℝ,0<D ∧ ∀i : HalfEndPhysicalSliceIndex,‖nativeH4MatchedScaleRawJetCLM B P hp i‖≤D := by
  obtain ⟨C,G,K,hC,hG,hK,h⟩ := exists_nativeBoundaryPoisson_all_scale_bounds P hp
    (nativeH4GraphSigmaCLM B P) (nativeH4GraphSigma_regular B P) (nativeH4GraphSigma_energy_bound B P)
  let N := ∑k : Fin 3,K k
  have hN : 0≤N := Finset.sum_nonneg (fun k _ => hK k)
  let L := 1+C+G+N
  have hL : 0<L := by dsimp only [L];linarith
  have hCL : C≤L := by dsimp only [L];linarith
  have hGL : G≤L := by dsimp only [L];linarith
  have hNL : N≤L := by dsimp only [L];linarith
  refine ⟨1+L,by positivity,fun i => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)⟩
  let b := nativeH4GraphSigmaCLM B P v
  have ht := h v i.1
  have h1 : ‖fun j => nativePoissonAllScaleFirst P hp i.1 b j‖≤G*‖v‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr ht.2.1
  have h2 : ‖fun k j => nativePoissonAllScaleSecond P hp i.1 b k j‖≤N*‖v‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact (ht.2.2 k j).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hK i) (Finset.mem_univ k)) (norm_nonneg v))
  have hJ : ‖(nativePoissonAllScaleValue P hp i.1 b,(fun j => nativePoissonAllScaleFirst P hp i.1 b j),
      (fun k j => nativePoissonAllScaleSecond P hp i.1 b k j))‖≤L*‖v‖ := by
    rw [Prod.norm_def,Prod.norm_def]
    exact max_le (ht.1.trans (mul_le_mul_of_nonneg_right hCL (norm_nonneg v)))
      (max_le (h1.trans (mul_le_mul_of_nonneg_right hGL (norm_nonneg v)))
        (h2.trans (mul_le_mul_of_nonneg_right hNL (norm_nonneg v))))
  have hF : ‖(nativeH4GraphScaleJetCLM i v).val‖≤‖v‖ := nativeH4GraphScaleJet_norm i v
  change ‖(nativeH4GraphScaleJetCLM i v).val+
    (nativePoissonAllScaleValue P hp i.1 b,(fun j => nativePoissonAllScaleFirst P hp i.1 b j),
      (fun k j => nativePoissonAllScaleSecond P hp i.1 b k j))‖≤_
  exact (norm_add_le _ _).trans ((add_le_add hF hJ).trans_eq (by ring))

#print axioms nativeH4GraphSigma_energy_bound
#print axioms nativeH4MatchedScale_memH2
#print axioms nativeH4MatchedScale_same_field
#print axioms exists_nativeH4MatchedScale_bound
end Yamabe3.Analysis.UniformElliptic
