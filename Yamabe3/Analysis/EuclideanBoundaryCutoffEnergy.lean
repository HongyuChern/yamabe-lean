import Yamabe3.Analysis.EuclideanSphereTrace
import Yamabe3.Analysis.ScaledBoundaryCutoffEnergy

/-!
# A boundary-layer cutoff estimate in actual three-dimensional volume

The endpoint term is the actual radius-a sphere integral, with its a²
area factor. The derivative energy is the genuine Euclidean derivative
of the same smooth function in the same collar. The proof uses actual
polar integration and retains the endpoint term until trace completion.

This is the smooth estimate needed for zero-trace exterior restriction.
It does not itself assert a trace-kernel theorem or discard values in
the excised ball.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace Yamabe3.Analysis.EuclideanSphereTrace

/-- The squared cutoff cost in a genuine collar of thickness 2δ.
Both constants are independent of a, δ and the same function f. -/
theorem integral_boundary_layer_sq_le_trace_and_derivative
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδa : 2 * δ ≤ a)
    {O : Set E} (hO : IsOpen O)
    (hKO : sphereTraceAnnulus a (a + 2 * δ) ⊆ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) :
    δ⁻¹ ^ 2 * (∫ x in sphereTraceAnnulus a (a + 2 * δ), f x ^ 2) ≤
      (16 / δ) * (∫ θ : S, f (a • (θ : E)) ^ 2
        ∂(ENNReal.ofReal (a ^ 2) • angularVolume)) +
      64 * ∫ x in sphereTraceAnnulus a (a + 2 * δ), ‖fderiv ℝ f x‖ ^ 2 := by
  have hfc := hf.continuousOn
  have hdc : ContinuousOn (fderiv ℝ f) O :=
    hf.continuousOn_fderiv_of_isOpen hO (by simp)
  have hfi : IntegrableOn (fun x => f x ^ 2) (sphereTraceAnnulus a (a + 2 * δ)) :=
    ((hfc.pow 2).mono hKO).integrableOn_compact
      (isCompact_sphereTraceAnnulus a (a + 2 * δ))
  have hdi : IntegrableOn (fun x => ‖fderiv ℝ f x‖ ^ 2)
      (sphereTraceAnnulus a (a + 2 * δ)) :=
    ((hdc.norm.pow 2).mono hKO).integrableOn_compact
      (isCompact_sphereTraceAnnulus a (a + 2 * δ))
  have hmap (θ : S) : MapsTo (fun t : ℝ => t • (θ : E))
      (Icc a (a + 2 * δ)) O :=
    fun t ht => hKO (radial_mem_sphereTraceAnnulus ha ht θ)
  have haa : a ∈ Icc a (a + 2 * δ) := ⟨le_rfl, by linarith⟩
  have htrace : Continuous (fun θ : S => f (a • (θ : E))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hc : ContinuousAt (fun q : S => a • (q : E)) θ := by
      simpa only [Pi.smul_apply] using!
        ((continuous_const : Continuous (fun _ : S => a)).smul
          (continuous_subtype_val : Continuous (Subtype.val : S → E))).continuousAt (x := θ)
    exact ContinuousAt.comp (f := fun q : S => a • (q : E))
      (hfc.continuousAt (hO.mem_nhds (hmap θ haa))) hc
  have hti : Integrable (fun θ : S => f (a • (θ : E)) ^ 2) angularVolume := by
    simpa only [integrableOn_univ, Pi.pow_apply] using!
      (htrace.pow 2).continuousOn.integrableOn_compact
        (μ := angularVolume) (isCompact_univ : IsCompact (univ : Set S))
  have hbound (θ : S) :
      δ⁻¹ ^ 2 * (∫ t in Icc a (a + 2 * δ), t ^ 2 * f (t • (θ : E)) ^ 2) ≤
        (16 * a ^ 2 / δ) * f (a • (θ : E)) ^ 2 +
          64 * ∫ t in Icc a (a + 2 * δ),
            t ^ 2 * ‖fderiv ℝ f (t • (θ : E))‖ ^ 2 := by
    let F : ℝ → ℝ := fun t => f (t • (θ : E))
    let D : ℝ → ℝ := fun t => fderiv ℝ f (t • (θ : E)) (θ : E)
    have hlin : Continuous (fun t : ℝ => t • (θ : E)) := continuous_id.smul continuous_const
    have hF : ContinuousOn F (Icc a (a + 2 * δ)) :=
      hfc.comp hlin.continuousOn (hmap θ)
    have hD : ContinuousOn D (Icc a (a + 2 * δ)) :=
      (hdc.comp hlin.continuousOn (hmap θ)).clm_apply continuousOn_const
    have hFD (t : ℝ) (ht : t ∈ Icc a (a + 2 * δ)) : HasDerivAt F (D t) t := by
      have h := (hf.contDiffAt (hO.mem_nhds (hmap θ ht))).differentiableAt (by simp)
      simpa only [F, D, Function.comp_def, one_smul] using!
        h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const (θ : E))
    have hFi : IntegrableOn (fun t => F t ^ 2) (Icc a (a + 2 * δ)) :=
      (hF.pow 2).integrableOn_compact isCompact_Icc
    have hDi : IntegrableOn (fun t => D t ^ 2) (Icc a (a + 2 * δ)) :=
      (hD.pow 2).integrableOn_compact isCompact_Icc
    have hWi : IntegrableOn (fun t => t ^ 2 * F t ^ 2) (Icc a (a + 2 * δ)) :=
      ((continuousOn_id.pow 2).mul (hF.pow 2)).integrableOn_compact isCompact_Icc
    have hEi : IntegrableOn
        (fun t => t ^ 2 * ‖fderiv ℝ f (t • (θ : E))‖ ^ 2) (Icc a (a + 2 * δ)) :=
      ((continuousOn_id.pow 2).mul
        ((hdc.comp hlin.continuousOn (hmap θ)).norm.pow 2)).integrableOn_compact isCompact_Icc
    have hupper : (∫ t in Icc a (a + 2 * δ), t ^ 2 * F t ^ 2) ≤
        (4 * a ^ 2) * ∫ t in Icc a (a + 2 * δ), F t ^ 2 := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on hWi (hFi.const_mul _) measurableSet_Icc
      intro t ht
      have ht0 := ha.le.trans ht.1
      have ht2 : t ≤ 2 * a := by linarith only [ht.2, hδa]
      have hsq := (sq_le_sq₀ ht0 (by positivity : 0 ≤ 2 * a)).mpr ht2
      have hsq' : t ^ 2 ≤ 4 * a ^ 2 := by nlinarith only [hsq]
      exact mul_le_mul_of_nonneg_right hsq' (sq_nonneg _)
    have htheta : ‖(θ : E)‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using θ.property
    have hderiv : a ^ 2 * (∫ t in Icc a (a + 2 * δ), D t ^ 2) ≤
        ∫ t in Icc a (a + 2 * δ), t ^ 2 * ‖fderiv ℝ f (t • (θ : E))‖ ^ 2 := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on (hDi.const_mul _) hEi measurableSet_Icc
      intro t ht
      have hd := (fderiv ℝ f (t • (θ : E))).le_opNorm (θ : E)
      rw [htheta, mul_one, Real.norm_eq_abs] at hd
      have hds : D t ^ 2 ≤ ‖fderiv ℝ f (t • (θ : E))‖ ^ 2 := by
        have hs := (sq_le_sq₀ (abs_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)).mpr hd
        simpa only [D, sq_abs] using hs
      have hat : a ^ 2 ≤ t ^ 2 := (sq_le_sq₀ ha.le (ha.le.trans ht.1)).mpr ht.1
      exact mul_le_mul hat hds (sq_nonneg _) (sq_nonneg _)
    have hscalar := SpherePolar.scaled_boundary_layer_energy_le a hδ hF hD hFD
    calc
      _ ≤ δ⁻¹ ^ 2 * ((4 * a ^ 2) * ∫ t in Icc a (a + 2 * δ), F t ^ 2) :=
        mul_le_mul_of_nonneg_left hupper (sq_nonneg _)
      _ = (4 * a ^ 2) * (δ⁻¹ ^ 2 * ∫ t in Icc a (a + 2 * δ), F t ^ 2) := by ring
      _ ≤ (4 * a ^ 2) * ((4 / δ) * F a ^ 2 +
          16 * ∫ t in Icc a (a + 2 * δ), D t ^ 2) :=
        mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ = (16 * a ^ 2 / δ) * F a ^ 2 +
          64 * (a ^ 2 * ∫ t in Icc a (a + 2 * δ), D t ^ 2) := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hderiv (by norm_num))
  have hJfi := integrable_sphereTraceAnnulus_polar_fiber ha hfi
  have hJdi := integrable_sphereTraceAnnulus_polar_fiber ha hdi
  calc
    _ = ∫ θ : S, δ⁻¹ ^ 2 *
        (∫ t in Icc a (a + 2 * δ), t ^ 2 * f (t • (θ : E)) ^ 2) ∂angularVolume := by
      rw [integral_const_mul, ← integral_sphereTraceAnnulus_native_polar ha hfi]
    _ ≤ ∫ θ : S, (16 * a ^ 2 / δ) * f (a • (θ : E)) ^ 2 +
        64 * (∫ t in Icc a (a + 2 * δ),
          t ^ 2 * ‖fderiv ℝ f (t • (θ : E))‖ ^ 2) ∂angularVolume :=
      integral_mono (hJfi.const_mul _) ((hti.const_mul _).add (hJdi.const_mul _)) hbound
    _ = _ := by
      rw [integral_add (hti.const_mul _) (hJdi.const_mul _), integral_const_mul,
        integral_const_mul, ← integral_sphereTraceAnnulus_native_polar ha hdi,
        integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg a), smul_eq_mul]
      ring

#print axioms integral_boundary_layer_sq_le_trace_and_derivative

end Yamabe3.Analysis.EuclideanSphereTrace
