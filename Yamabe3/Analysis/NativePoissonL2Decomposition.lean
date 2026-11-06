import Yamabe3.Analysis.SpectralBoundaryPoissonL2
import Yamabe3.Analysis.NativeFreeTailIdentification
import Yamabe3.Analysis.NativeHighPoissonCoefficient

/-! The original potential Poisson field is the same free field minus
one actual L2-source particular solution. The positive-time identity
preserves its original entrance inverse and native high projection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

def nativePoissonAuxiliary (P : NativeHighPotential) (b : AngularH1) : SpectralSpace AngularIndex :=
  angularBasis.repr (angularEmbedding
    (nativeHighEnergyEntranceCLM P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg b))

def nativePoissonL2CorrectionSource (P : NativeHighPotential) (b : AngularH1) :
    Lp (SpectralSpace AngularIndex) 2 (volume : Measure ℝ) :=
  (spectralFullBoundaryPoisson_potential_memLp nativeAngularRate (by norm_num) nativeAngularRate_lower
    P.potential (nativePoissonAuxiliary P b)).toLp
      ((P.potential • spectralFullBoundaryPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
        (nativePoissonAuxiliary P b) : ℝ →ᵇ SpectralSpace AngularIndex) : ℝ → SpectralSpace AngularIndex)

 theorem nativePoissonCurve_high (P : NativeHighPotential) (b : AngularH1) (t : ℝ) :
    nativeHighProjection (P.curve b t)=P.curve b t := by
  apply angularBasis.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply,nativeHighProjection,
    nativeAngularProjection_coefficient]
  split_ifs with hi
  · rfl
  · exact (P.curve_low_zero b i (lt_of_not_ge hi) t).symm

 theorem nativePoissonCurve_full_spectral (P : NativeHighPotential) (b : AngularH1)
    (t : ℝ) (ht : 0 ≤ t) :
    P.curve b t=Real.exp (-2*t) • angularBasis.repr.symm
      (spectralFullBoundaryPoissonCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
          (nativePoissonAuxiliary P b) t-
        spectralHalfFullPotentialCorrectionCLM nativeAngularRate (by norm_num) nativeAngularRate_lower
          P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound (nativePoissonAuxiliary P b) t) := by
  rw [NativeHighPotential.curve,nativeHalfHighPotentialPhysical,nativeHalfHighPotentialPoissonCLM_apply,
    spectralHalfPotentialPoissonCLM_apply,←nativeHighEnergyEntranceCLM_embedding_repr,
    Real.coe_toNNReal t ht]
  rfl

 theorem nativePoissonCurve_same_L2_correction (P : NativeHighPotential)
    (hplus : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|) ≤ P.κ)
    (b : AngularH1) (t : ℝ) (ht : 0 ≤ t) :
    P.curve b t=
      nativeConjugatedCurve (nativeFreeBoundaryAngular (nativePoissonAuxiliary P b)) t-
      nativeConjugatedCurve (nativeL2ParticularAngularCLM P.potential (nativePoissonL2CorrectionSource P b)) t := by
  have h := congrArg nativeHighProjection (nativePoissonCurve_full_spectral P b t ht)
  rw [nativePoissonCurve_high,map_smul,map_sub,map_sub] at h
  have hc := spectralHalfFullCorrection_eq_L2 nativeAngularRate (by norm_num) nativeAngularRate_lower
    P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound hplus (nativePoissonAuxiliary P b)
  rw [hc,smul_sub] at h
  exact h

#print axioms nativePoissonCurve_high
#print axioms nativePoissonCurve_full_spectral
#print axioms nativePoissonCurve_same_L2_correction
end Yamabe3.Analysis.SpherePolar
