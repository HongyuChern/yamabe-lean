import Yamabe3.Analysis.NativeForcedHalfEndStrongDerivative

/-!
# Bounded linear source maps for the actual strong derivative

Linearity is proved from the original solution operator and uniqueness
of its actual right derivative.  The resulting bounded continuous curve
is literally `exp(2t)` times that same strong derivative.  Evaluating it
at zero gives a bounded linear map to the actual entrance right derivative.

The source difference estimates are in the stated bounded-continuous
source norm.  They do not assert convergence of an unspecified spectral
net, and no geometric conormal interpretation is introduced here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Filter MeasureTheory PoincareMT
open scoped NNReal Topology lp RealInnerProductSpace BoundedContinuousFunction

namespace Yamabe3.Analysis.Delaunay

open SphereSpectrum

/-- The explicit derivative coefficient from the proved strong estimate. -/
def nativeHalfHighDirichletDerivativeBound (κ : ℝ) (V : ℝ →ᵇ ℝ) : ℝ :=
  (10 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)) +
    (1 + (10 / 9 : ℝ) * ‖V‖ / (1 - κ)) *
      ((20 / 9 : ℝ) * (1 + (4 / 9 : ℝ) * ‖V‖ / (1 - κ)))

theorem nativeHalfHighDirichletDerivativeBound_nonneg
    {κ : ℝ} (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ) :
    0 ≤ nativeHalfHighDirichletDerivativeBound κ V := by
  have hκ : 0 < 1 - κ := sub_pos.mpr hκ1
  unfold nativeHalfHighDirichletDerivativeBound
  positivity

variable {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
  (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) (-2) s * |V (t - s)|) ≤ κ)
  (hV0 : ∀ t, 0 ≤ V t)

theorem nativeHalfHighDirichletPhysical_add
    (F G : ℝ≥0 →ᵇ AngularL2) (t : ℝ) :
    nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 (F + G) t =
      nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t +
        nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 G t := by
  simp only [nativeHalfHighDirichletPhysical, map_add,
    BoundedContinuousFunction.add_apply, smul_add]

theorem nativeHalfHighDirichletPhysical_smul
    (c : ℝ) (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) :
    nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 (c • F) t =
      c • nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F t := by
  simp only [nativeHalfHighDirichletPhysical, map_smul,
    BoundedContinuousFunction.smul_apply, RingHom.id_apply]
  exact smul_comm _ _ _

/-- Linearity of the actual derivative follows from right-derivative
uniqueness for the same original solution curves. -/
theorem nativeHalfHighDirichletPhysicalDerivative_add
    (F G : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : 0 ≤ t) :
    nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 (F + G) t =
      nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t +
        nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 G t := by
  have hsum := (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 F t ht).add
    (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 G t ht)
  have hsame : HasDerivWithinAt (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 (F + G))
      (nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t +
        nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 G t) (Ici 0) t :=
    hsum.congr_of_mem (fun s _hs => nativeHalfHighDirichletPhysical_add hκ0 hκ1 V hV hV0 F G s) ht
  exact (uniqueDiffOn_Ici (0 : ℝ) t ht).eq_deriv _
    (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 (F + G) t ht) hsame

theorem nativeHalfHighDirichletPhysicalDerivative_smul
    (c : ℝ) (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ) (ht : 0 ≤ t) :
    nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 (c • F) t =
      c • nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t := by
  have hc := HasDerivWithinAt.const_smul c
    (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 F t ht)
  have hsame : HasDerivWithinAt (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 (c • F))
      (c • nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F t) (Ici 0) t :=
    hc.congr_of_mem (fun s _hs => nativeHalfHighDirichletPhysical_smul hκ0 hκ1 V hV hV0 c F s) ht
  exact (uniqueDiffOn_Ici (0 : ℝ) t ht).eq_deriv _
    (nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 (c • F) t ht) hsame

/-- The genuine bounded continuous curve of weighted strong derivatives. -/
def nativeHalfHighDirichletWeightedDerivative (F : ℝ≥0 →ᵇ AngularL2) : ℝ≥0 →ᵇ AngularL2 :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => Real.exp (2 * (t : ℝ)) •
      nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F (t : ℝ))
    ((by fun_prop : Continuous (fun t : ℝ≥0 => Real.exp (2 * (t : ℝ)))).smul
      ((nativeHalfHighDirichletPhysicalDerivative_continuous hκ0 hκ1 V hV hV0 F).comp
        continuous_subtype_val))
    (nativeHalfHighDirichletDerivativeBound κ V * ‖F‖)
    (fun t => by
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact nativeHalfHighDirichletPhysicalDerivative_weighted_norm_le
        hκ0 hκ1 V hV hV0 F (t : ℝ) t.coe_nonneg)

theorem nativeHalfHighDirichletWeightedDerivative_apply
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ≥0) :
    nativeHalfHighDirichletWeightedDerivative hκ0 hκ1 V hV hV0 F t =
      Real.exp (2 * (t : ℝ)) •
        nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F (t : ℝ) := rfl

theorem nativeHalfHighDirichletWeightedDerivative_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletWeightedDerivative hκ0 hκ1 V hV hV0 F‖ ≤
      nativeHalfHighDirichletDerivativeBound κ V * ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (nativeHalfHighDirichletDerivativeBound_nonneg hκ1 V) (norm_nonneg F))).mpr
  intro t
  rw [nativeHalfHighDirichletWeightedDerivative_apply, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  exact nativeHalfHighDirichletPhysicalDerivative_weighted_norm_le
    hκ0 hκ1 V hV hV0 F (t : ℝ) t.coe_nonneg

/-- A source-to-derivative continuous linear map of the actual curves. -/
def nativeHalfHighDirichletWeightedDerivativeCLM :
    (ℝ≥0 →ᵇ AngularL2) →L[ℝ] (ℝ≥0 →ᵇ AngularL2) :=
  ({ toFun := nativeHalfHighDirichletWeightedDerivative hκ0 hκ1 V hV hV0
     map_add' := by
       intro F G
       apply BoundedContinuousFunction.ext
       intro t
       simp only [nativeHalfHighDirichletWeightedDerivative_apply,
         BoundedContinuousFunction.add_apply,
         nativeHalfHighDirichletPhysicalDerivative_add hκ0 hκ1 V hV hV0 F G
           (t : ℝ) t.coe_nonneg, smul_add]
     map_smul' := by
       intro c F
       apply BoundedContinuousFunction.ext
       intro t
       simp only [nativeHalfHighDirichletWeightedDerivative_apply,
         BoundedContinuousFunction.smul_apply, RingHom.id_apply,
         nativeHalfHighDirichletPhysicalDerivative_smul hκ0 hκ1 V hV hV0 c F
           (t : ℝ) t.coe_nonneg]
       exact smul_comm _ _ _ } :
      (ℝ≥0 →ᵇ AngularL2) →ₗ[ℝ] (ℝ≥0 →ᵇ AngularL2)).mkContinuous
    (nativeHalfHighDirichletDerivativeBound κ V)
    (nativeHalfHighDirichletWeightedDerivative_norm_le hκ0 hκ1 V hV hV0)

theorem nativeHalfHighDirichletWeightedDerivativeCLM_apply
    (F : ℝ≥0 →ᵇ AngularL2) (t : ℝ≥0) :
    nativeHalfHighDirichletWeightedDerivativeCLM hκ0 hκ1 V hV hV0 F t =
      Real.exp (2 * (t : ℝ)) •
        nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F (t : ℝ) := rfl

theorem nativeHalfHighDirichletWeightedDerivativeCLM_source_difference
    (F G : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletWeightedDerivativeCLM hκ0 hκ1 V hV hV0 F -
      nativeHalfHighDirichletWeightedDerivativeCLM hκ0 hκ1 V hV hV0 G‖ ≤
      nativeHalfHighDirichletDerivativeBound κ V * ‖F - G‖ := by
  rw [← map_sub]
  exact nativeHalfHighDirichletWeightedDerivative_norm_le hκ0 hκ1 V hV hV0 (F - G)

/-- Evaluation at zero of the actual weighted strong derivative map. -/
def nativeHalfHighDirichletEntranceDerivativeCLM :
    (ℝ≥0 →ᵇ AngularL2) →L[ℝ] AngularL2 :=
  (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) (0 : ℝ≥0)).comp
    (nativeHalfHighDirichletWeightedDerivativeCLM hκ0 hκ1 V hV hV0)

theorem nativeHalfHighDirichletEntranceDerivativeCLM_apply (F : ℝ≥0 →ᵇ AngularL2) :
    nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F =
      nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F 0 := by
  change Real.exp (2 * ((0 : ℝ≥0) : ℝ)) •
    nativeHalfHighDirichletPhysicalDerivative hκ0 hκ1 V hV hV0 F ((0 : ℝ≥0) : ℝ) = _
  simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_smul]

theorem nativeHalfHighDirichletEntranceDerivativeCLM_hasDerivWithinAt
    (F : ℝ≥0 →ᵇ AngularL2) :
    HasDerivWithinAt (nativeHalfHighDirichletPhysical hκ0 hκ1 V hV hV0 F)
      (nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F) (Ici 0) 0 := by
  rw [nativeHalfHighDirichletEntranceDerivativeCLM_apply]
  exact nativeHalfHighDirichletPhysical_hasDerivWithinAt hκ0 hκ1 V hV hV0 F 0 le_rfl

theorem nativeHalfHighDirichletEntranceDerivativeCLM_norm_le (F : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F‖ ≤
      nativeHalfHighDirichletDerivativeBound κ V * ‖F‖ := by
  exact ((nativeHalfHighDirichletWeightedDerivative hκ0 hκ1 V hV hV0 F).norm_coe_le_norm 0).trans
    (nativeHalfHighDirichletWeightedDerivative_norm_le hκ0 hκ1 V hV hV0 F)

theorem nativeHalfHighDirichletEntranceDerivativeCLM_source_difference
    (F G : ℝ≥0 →ᵇ AngularL2) :
    ‖nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 F -
      nativeHalfHighDirichletEntranceDerivativeCLM hκ0 hκ1 V hV hV0 G‖ ≤
      nativeHalfHighDirichletDerivativeBound κ V * ‖F - G‖ := by
  rw [← map_sub]
  exact nativeHalfHighDirichletEntranceDerivativeCLM_norm_le hκ0 hκ1 V hV hV0 (F - G)

#print axioms nativeHalfHighDirichletPhysicalDerivative_add
#print axioms nativeHalfHighDirichletPhysicalDerivative_smul
#print axioms nativeHalfHighDirichletWeightedDerivativeCLM
#print axioms nativeHalfHighDirichletWeightedDerivativeCLM_source_difference
#print axioms nativeHalfHighDirichletEntranceDerivativeCLM
#print axioms nativeHalfHighDirichletEntranceDerivativeCLM_hasDerivWithinAt
#print axioms nativeHalfHighDirichletEntranceDerivativeCLM_source_difference

end Yamabe3.Analysis.Delaunay
