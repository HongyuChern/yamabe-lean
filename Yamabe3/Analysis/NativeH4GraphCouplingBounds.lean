import Yamabe3.Analysis.NativeH4GraphCoupling
import Yamabe3.Analysis.NativeBoundaryPoissonOperators

/-! The same coupled correction has a uniform spectral energy budget.
The constant precedes the inner potential and every input graph element.
Neither pointwise sourcewise constants nor a new boundary hypothesis are
substituted for this operator estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay

theorem nativeH1_norm_sq_le_three_halves (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    ‖b‖^2≤∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i := by
  obtain ⟨c,hc,hbnd⟩ := nativeAngular_three_halves_exists_H1 (angularEmbedding b) hb
  have he : c=b := angularEmbedding_injective hc
  simpa only [he] using hbnd

theorem nativePoisson_energy_le_three_halves (b : AngularH1)
    (hb : NativeAngularSpectralRegular (3/2) (angularEmbedding b)) :
    nativePoissonBoundaryEnergy b≤2*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) := by
  have h := nativeH1_norm_sq_le_three_halves b hb
  unfold nativePoissonBoundaryEnergy
  linarith

theorem nativeAngularSpectralRegular_add {s : ℝ} {f g : AngularL2}
    (hf : NativeAngularSpectralRegular s f) (hg : NativeAngularSpectralRegular s g) :
    NativeAngularSpectralRegular s (f+g) ∧
      (∑'i,nativeAngularWeightedSquare s (f+g) i)≤
        2*((∑'i,nativeAngularWeightedSquare s f i)+(∑'i,nativeAngularWeightedSquare s g i)) := by
  have hn := nativeAngularSpectralRegular_smul hg (-1)
  have h := nativeAngularSpectralRegular_sub hf hn.1
  simp only [neg_one_smul,sub_neg_eq_add] at h hn
  exact ⟨h.1,by linarith only [h.2,hn.2]⟩

def nativeH4GraphExteriorDatumCLM (B P : NativeHighPotential) : HalfEndPhysicalH4Graph →L[ℝ] AngularH1 :=
  nativeH4GraphSigmaCLM B P+nativeH4GraphHighValueCLM

theorem nativeH4GraphExteriorDatum_regular (B P : NativeHighPotential) (v : HalfEndPhysicalH4Graph) :
    NativeAngularSpectralRegular (3/2) (angularEmbedding (nativeH4GraphExteriorDatumCLM B P v)) := by
  change NativeAngularSpectralRegular (3/2) (angularEmbedding (nativeH4GraphSigmaCLM B P v+nativeH4GraphHighValueCLM v))
  rw [map_add]
  exact (nativeAngularSpectralRegular_add (nativeH4GraphSigma_regular B P v) (nativeH4GraphHighValue_regular v)).1

theorem exists_nativeH4Graph_coupling_energy_bound (B : NativeHighPotential) :
    ∃C : ℝ,0≤C ∧ ∀(P : NativeHighPotential) (v : HalfEndPhysicalH4Graph),
      nativePoissonBoundaryEnergy (nativeH4GraphSigmaCLM B P v)≤C*‖v‖^2 ∧
      nativePoissonBoundaryEnergy (nativeH4GraphExteriorDatumCLM B P v)≤C*‖v‖^2 := by
  obtain ⟨D,hD,hd⟩ := nativeAngularSpectral_uniform_bound
    (angularEmbedding.comp nativeH4GraphHighValueCLM) (3/2) nativeH4GraphHighValue_regular
  obtain ⟨N,hN,hn⟩ := nativeAngularSpectral_uniform_bound
    nativeH4GraphNormalJumpCLM (1/2) nativeH4GraphNormalJump_regular
  let A := 8*(N+B.derivativeBound^2*D)
  have hA : 0≤A := by dsimp only [A];positivity
  refine ⟨4*(A+D),by positivity,fun P v => ?_⟩
  have hS := nativeHighCoupled_cauchy_spectral_regular B P (nativeH4GraphHighValueCLM v)
    (nativeH4GraphNormalJumpCLM v) (1/2)
    (by convert nativeH4GraphHighValue_regular v using 1 <;> norm_num)
    (nativeH4GraphNormalJump_regular v)
  have hs : (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeH4GraphSigmaCLM B P v)) i)≤
      8*((∑'i,nativeAngularWeightedSquare (1/2) (nativeH4GraphNormalJumpCLM v) i)+
        B.derivativeBound^2*(∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeH4GraphHighValueCLM v)) i)) := by
    convert hS.2 using 1 <;> norm_num [nativeH4GraphSigmaCLM,ContinuousLinearMap.comp_apply,sub_apply]
  have hdv : (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeH4GraphHighValueCLM v)) i)≤D*‖v‖^2 := hd v
  have hnV := hn v
  have hsA : (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeH4GraphSigmaCLM B P v)) i)≤A*‖v‖^2 := by
    have hm := mul_le_mul_of_nonneg_left hdv (sq_nonneg B.derivativeBound)
    dsimp only [A]
    nlinarith only [hs,hm,hnV]
  have hi := nativePoisson_energy_le_three_halves _ (nativeH4GraphSigma_regular B P v)
  have he := nativePoisson_energy_le_three_halves _ (nativeH4GraphExteriorDatum_regular B P v)
  have ha := (nativeAngularSpectralRegular_add (nativeH4GraphSigma_regular B P v)
    (nativeH4GraphHighValue_regular v)).2
  have ha' : (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeH4GraphExteriorDatumCLM B P v)) i)≤
      2*((∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeH4GraphSigmaCLM B P v)) i)+
        (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (nativeH4GraphHighValueCLM v)) i)) := by
    change (∑'i,nativeAngularWeightedSquare (3/2) (angularEmbedding (_+_)) i)≤_
    rw [map_add]
    exact ha
  constructor
  · nlinarith only [hi,hsA,mul_nonneg hA (sq_nonneg ‖v‖),mul_nonneg hD (sq_nonneg ‖v‖)]
  · nlinarith only [he,ha',hsA,hdv]

#print axioms nativeH1_norm_sq_le_three_halves
#print axioms nativePoisson_energy_le_three_halves
#print axioms nativeAngularSpectralRegular_add
#print axioms nativeH4GraphExteriorDatum_regular
#print axioms exists_nativeH4Graph_coupling_energy_bound
end Yamabe3.Analysis.UniformElliptic
