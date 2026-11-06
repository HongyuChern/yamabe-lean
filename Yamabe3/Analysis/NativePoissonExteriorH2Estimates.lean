import Yamabe3.Analysis.NativePoissonExteriorFiniteCollar
import Yamabe3.Analysis.NativePolarCollarGeometry
import Yamabe3.Analysis.NativeC2GradientEstimate
import Yamabe3.Analysis.UniformElliptic.NativeLocalStrongEquation

/-! The actual finite Poisson fields have uniform physical first and
second derivative estimates on a collar crossing the entrance. Bounds
retain finite frequency sums, for subsequent difference estimates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay Yamabe3.Analysis.UniformElliptic

theorem nativePoissonExteriorFiniteCollar_H2_estimates (P : NativeHighPotential) :
    ∃ (G : ℝ) (K : Fin 3 → ℝ),0 ≤ G ∧ (∀ k,0 ≤ K k) ∧
      ∀ (b : AngularH1) (s : Finset AngularIndex),
      let u := nativePoissonExteriorFiniteCollar P b s
      let V := nativePolarTimeWindow (Ioo (-(1/2:ℝ)) (1/2))
      (∫ x in V,∑ j : Fin 3,nativeCoordinateFirst j u x^2) ≤
        G*(∑ i ∈ s,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i) ∧
      ∀ k i : Fin 3,eLpNorm (nativeCoordinateSecond k i u) 2 (volume.restrict V) ≤
        ENNReal.ofReal (Real.sqrt (K k*(∑ i ∈ s,nativeAngularWeightedSquare (3/2) (angularEmbedding b) i))) := by
  let O : Set E := {0}ᶜ
  let W := nativePolarTimeWindow (Ioo (-1) 1)
  let V := nativePolarTimeWindow (Ioo (-(1/2:ℝ)) (1/2))
  have hO : IsOpen O := isClosed_singleton.isOpen_compl
  have hW : IsOpen W := nativePolarTimeWindow_open 1
  have hWc : IsCompact (closure W) := nativePolarTimeWindow_precompact 1
  have hWO : closure W ⊆ O := nativePolarTimeWindow_closure_offZero 1
  have hV : IsOpen V := nativePolarTimeWindow_open (1/2)
  have hVc : IsCompact (closure V) := nativePolarTimeWindow_precompact (1/2)
  have hVW : closure V ⊆ W := nativePolarTimeWindow_nested (by norm_num : (1/2:ℝ)<1)
  obtain ⟨G,hG,hgrad⟩ := exists_uniform_C2_local_gradient_estimate hO hW hWc hWO hV hVc hVW
  obtain ⟨K,hK,hhess⟩ := exists_uniform_C2_local_hessian_estimate hO hW hWc hWO hV hVc hVW
  let A := 12000*Real.exp 2*(4+P.derivativeBound)
  have hA : 0 ≤ A := by have h := P.derivativeBound_nonneg; dsimp [A]; positivity
  refine ⟨G*A,fun k => K k*A,mul_nonneg hG hA,fun k => mul_nonneg (hK k) hA,?_⟩
  intro b s
  have h := nativePoissonExteriorFiniteCollar_finite_energy P b s
  dsimp only
  constructor
  · have hg := hgrad (nativePoissonExteriorFiniteCollar P b s) h.1
    apply hg.trans
    have he := mul_le_mul_of_nonneg_left h.2.2.2 hG
    simpa only [A,mul_assoc] using he
  · intro k i
    apply (hhess (nativePoissonExteriorFiniteCollar P b s) h.1 k i).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    have he := mul_le_mul_of_nonneg_left h.2.2.2 (hK k)
    simpa only [A,mul_assoc] using he

#print axioms nativePoissonExteriorFiniteCollar_H2_estimates
end Yamabe3.Analysis.SpherePolar
