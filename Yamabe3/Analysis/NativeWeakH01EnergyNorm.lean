import Yamabe3.Analysis.NativeWeakH01EnergyIdentity

/-!
# Exact native energy norm of the original weak realization

Strong convergence identifies the full completed norm with the original
value and coordinate derivative square integrals. This transports actual
quantitative estimates, without a new arbitrary completion constant.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal

namespace Yamabe3.Analysis.SpherePolar

open PoincareMT.LeviCivitaData.Dirichlet UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "D" => nativeWeakEuclideanD

private def weakNormTestNormedSpace (O : Set E) :
    NormedSpace ℝ (EnergyTest D O) := inferInstance
private def weakNormNormedSpace (O : Set E) :
    NormedSpace ℝ (H1Zero D O) := inferInstance
attribute [local instance] weakNormTestNormedSpace weakNormNormedSpace

/-- Exact equality of the completed norm and the original three weak
derivative integrals. The coefficient eight belongs to the PDE form,
not to this inhomogeneous H1 norm. -/
theorem nativeEuclidean_norm_sq_of_weak_approximation
    {O : Set E} (hO : IsOpen O)
    (φ : ℕ → EnergyTest D O) (u : E → ℝ) (du : E → E)
    (hu : MemLp u 2 (volume.restrict O))
    (hdu : ∀ i : Fin 3, MemLp (fun x => du x i) 2 (volume.restrict O))
    (hv : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2
      (volume.restrict O)) atTop (𝓝 0))
    (hd : ∀ i : Fin 3, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (φ n : E → ℝ) x (EuclideanSpace.single i 1) - du x i)
      2 (volume.restrict O)) atTop (𝓝 0))
    (z : H1Zero D O)
    (hzrep : (toL2 D O z : E → ℝ) =ᵐ[volume] O.indicator u) :
    ‖z‖ ^ 2 = (∫ x in O, u x ^ 2) +
      ∑ i : Fin 3, ∫ x in O, du x i ^ 2 := by
  have hz := nativeEuclidean_approximation_tendsto_to_rep
    hO φ u du hu hdu hv hd z hzrep
  have hnorm := hz.norm.pow 2
  simp only [Completion.norm_coe] at hnorm
  let hm (n : ℕ) : MemLp (φ n : E → ℝ) 2 (volume.restrict O) :=
    ((φ n).smooth.continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport).restrict O
  have hvalue : Tendsto (fun n => (hm n).toLp (φ n : E → ℝ))
      atTop (𝓝 (hu.toLp u)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr hv
  have hvalueSq : Tendsto (fun n => ∫ x in O, φ n x ^ 2) atTop
      (𝓝 (∫ x in O, u x ^ 2)) := by
    simpa only [native_norm_toLp_sq_eq_integral_sq] using hvalue.norm.pow 2
  have hderivativeSq (i : Fin 3) :
      Tendsto (fun n => ∫ x in O,
        (fderiv ℝ (φ n : E → ℝ) x (EuclideanSpace.single i 1)) ^ 2)
        atTop (𝓝 (∫ x in O, du x i ^ 2)) := by
    have hderivative : Tendsto (fun n =>
        ((nativeEuclidean_test_derivative_memLp O (φ n) i).restrict O).toLp
          (fun x => fderiv ℝ (φ n : E → ℝ) x (EuclideanSpace.single i 1)))
        atTop (𝓝 ((hdu i).toLp (fun x => du x i))) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr (hd i)
    simpa only [native_norm_toLp_sq_eq_integral_sq] using hderivative.norm.pow 2
  have hsum := hvalueSq.add (tendsto_finsetSum Finset.univ (fun i _ => hderivativeSq i))
  have hnorm' : Tendsto (fun n => ‖φ n‖ ^ 2) atTop
      (𝓝 ((∫ x in O, u x ^ 2) + ∑ i : Fin 3, ∫ x in O, du x i ^ 2)) := by
    simpa only [nativeEuclidean_test_norm_sq_restrict hO.measurableSet] using hsum
  exact tendsto_nhds_unique hnorm hnorm'

#print axioms nativeEuclidean_norm_sq_of_weak_approximation

end Yamabe3.Analysis.SpherePolar
