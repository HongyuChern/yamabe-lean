import Yamabe3.Analysis.Cylinder.NativeSphereRestriction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Algebra.Support

/-!
# A genuine smooth cutoff family for the punctured unit ball

The cutoff is the literal product of two fixed smooth transitions in
the squared Euclidean radius.  For positive epsilon its support stays
between squared radii epsilon and `1-epsilon`; it is one between squared
radii `2*epsilon` and `1-2*epsilon`.

The single transition's derivative is bounded by compactness on `[0,1]`
and by its actual zero derivative on the two constant regions.  The
chain and product rules then give one constant K, chosen before epsilon
and the spatial point, with `norm (fderiv cutoff) <= K / epsilon`.
The derivative vanishes on the open middle region, so its topological
support is contained in the two closed boundary layers.

These are proved geometric properties of one explicit smooth family.
No zero-boundary Sobolev membership or trace statement is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace Yamabe3.Analysis.SpherePolar

/-- The fixed smooth transition applied to the actual squared radius
at the two ends of the punctured unit ball. -/
def nativePuncturedUnitBallCutoff (ε : ℝ) (x : E) : ℝ :=
  Real.smoothTransition ((‖x‖ ^ 2 - ε) / ε) *
    Real.smoothTransition ((1 - ε - ‖x‖ ^ 2) / ε)

theorem nativePuncturedUnitBallCutoff_contDiff (ε : ℝ) :
    ContDiff ℝ ∞ (nativePuncturedUnitBallCutoff ε) := by
  have hq : ContDiff ℝ ∞ (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  unfold nativePuncturedUnitBallCutoff
  exact (Real.smoothTransition.contDiff.comp ((hq.sub contDiff_const).div_const ε)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε))

theorem nativePuncturedUnitBallCutoff_range (ε : ℝ) (x : E) :
    0 ≤ nativePuncturedUnitBallCutoff ε x ∧ nativePuncturedUnitBallCutoff ε x ≤ 1 := by
  unfold nativePuncturedUnitBallCutoff
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _)).trans (by
        simpa only [one_mul] using Real.smoothTransition.le_one ((1 - ε - ‖x‖ ^ 2) / ε))

private theorem cutoff_zero_inner (ε : ℝ) (hε : 0 < ε) (x : E) (hx : ‖x‖ ^ 2 ≤ ε) :
    nativePuncturedUnitBallCutoff ε x = 0 := by
  have ha : (‖x‖ ^ 2 - ε) / ε ≤ 0 := (div_le_iff₀ hε).mpr (by linarith)
  simp only [nativePuncturedUnitBallCutoff, Real.smoothTransition.zero_of_nonpos ha, zero_mul]

private theorem cutoff_zero_outer (ε : ℝ) (hε : 0 < ε) (x : E)
    (hx : 1 - ε ≤ ‖x‖ ^ 2) : nativePuncturedUnitBallCutoff ε x = 0 := by
  have hb : (1 - ε - ‖x‖ ^ 2) / ε ≤ 0 := (div_le_iff₀ hε).mpr (by linarith)
  simp only [nativePuncturedUnitBallCutoff, Real.smoothTransition.zero_of_nonpos hb, mul_zero]

/-- The actual topological support stays in a closed annulus strictly
inside the punctured unit ball whenever epsilon is positive. -/
theorem nativePuncturedUnitBallCutoff_tsupport_annulus (ε : ℝ) (hε : 0 < ε) :
    tsupport (nativePuncturedUnitBallCutoff ε) ⊆
      {x : E | ε ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ 1 - ε} := by
  have hclosed : IsClosed {x : E | ε ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ 1 - ε} :=
    (isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)
  change closure (Function.support (nativePuncturedUnitBallCutoff ε)) ⊆ _
  apply closure_minimal ?_ hclosed
  intro x hx
  constructor
  · by_contra h
    exact hx (cutoff_zero_inner ε hε x (lt_of_not_ge h).le)
  · by_contra h
    exact hx (cutoff_zero_outer ε hε x (lt_of_not_ge h).le)

theorem nativePuncturedUnitBallCutoff_tsupport_subset (ε : ℝ) (hε : 0 < ε) :
    tsupport (nativePuncturedUnitBallCutoff ε) ⊆
      Metric.ball (0 : E) 1 \ {(0 : E)} := by
  intro x hx
  obtain ⟨hl, hu⟩ := nativePuncturedUnitBallCutoff_tsupport_annulus ε hε hx
  have hx0 : x ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hl
    exact (not_le_of_gt hε) hl
  refine ⟨?_, by simpa only [mem_singleton_iff] using hx0⟩
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith only [hu, hε, sq_nonneg (‖x‖ - 1)]

theorem nativePuncturedUnitBallCutoff_hasCompactSupport (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (nativePuncturedUnitBallCutoff ε) := by
  change IsCompact (tsupport (nativePuncturedUnitBallCutoff ε))
  apply (isCompact_closedBall (0 : E) 1).of_isClosed_subset
    (isClosed_tsupport (nativePuncturedUnitBallCutoff ε))
  intro x hx
  exact Metric.mem_closedBall.mpr
    (Metric.mem_ball.mp ((nativePuncturedUnitBallCutoff_tsupport_subset ε hε hx).1)).le

/-- On the entire closed middle annulus the explicit cutoff is exactly
one.  The assumed annulus is nonempty for the intended epsilon range. -/
theorem nativePuncturedUnitBallCutoff_eq_one (ε : ℝ) (hε : 0 < ε) (x : E)
    (hlo : 2 * ε ≤ ‖x‖ ^ 2) (hhi : ‖x‖ ^ 2 ≤ 1 - 2 * ε) :
    nativePuncturedUnitBallCutoff ε x = 1 := by
  have ha : 1 ≤ (‖x‖ ^ 2 - ε) / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hb : 1 ≤ (1 - ε - ‖x‖ ^ 2) / ε := (le_div_iff₀ hε).mpr (by linarith)
  simp only [nativePuncturedUnitBallCutoff, Real.smoothTransition.one_of_one_le ha,
    Real.smoothTransition.one_of_one_le hb, one_mul]

/-- The derivative really vanishes in the open middle annulus, by local
constancy of the same cutoff. -/
theorem nativePuncturedUnitBallCutoff_fderiv_eq_zero (ε : ℝ) (hε : 0 < ε) (x : E)
    (hlo : 2 * ε < ‖x‖ ^ 2) (hhi : ‖x‖ ^ 2 < 1 - 2 * ε) :
    fderiv ℝ (nativePuncturedUnitBallCutoff ε) x = 0 := by
  have hnbh : {y : E | 2 * ε < ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 < 1 - 2 * ε} ∈ 𝓝 x :=
    ((isOpen_lt continuous_const (continuous_norm.pow 2)).inter
      (isOpen_lt (continuous_norm.pow 2) continuous_const)).mem_nhds ⟨hlo, hhi⟩
  have heq : nativePuncturedUnitBallCutoff ε =ᶠ[𝓝 x] (fun _ : E => (1 : ℝ)) := by
    filter_upwards [hnbh] with y hy
    exact nativePuncturedUnitBallCutoff_eq_one ε hε y hy.1.le hy.2.le
  exact ((hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq heq).fderiv

/-- The topological support of the actual derivative lies in the two
closed endpoint layers.  The middle boundary surfaces are retained. -/
theorem nativePuncturedUnitBallCutoff_fderiv_tsupport_subset (ε : ℝ) (hε : 0 < ε) :
    tsupport (fderiv ℝ (nativePuncturedUnitBallCutoff ε)) ⊆
      {x : E | ‖x‖ ^ 2 ≤ 2 * ε ∨ 1 - 2 * ε ≤ ‖x‖ ^ 2} := by
  have hclosed : IsClosed {x : E | ‖x‖ ^ 2 ≤ 2 * ε ∨ 1 - 2 * ε ≤ ‖x‖ ^ 2} :=
    (isClosed_le (continuous_norm.pow 2) continuous_const).union
      (isClosed_le continuous_const (continuous_norm.pow 2))
  change closure (Function.support (fderiv ℝ (nativePuncturedUnitBallCutoff ε))) ⊆ _
  apply closure_minimal ?_ hclosed
  intro x hx
  by_cases hlo : ‖x‖ ^ 2 ≤ 2 * ε
  · exact Or.inl hlo
  · apply Or.inr
    by_contra hhi
    exact hx (nativePuncturedUnitBallCutoff_fderiv_eq_zero ε hε x
      (lt_of_not_ge hlo) (lt_of_not_ge hhi))

private theorem smoothTransition_deriv_norm_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ B := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ 2 Real.smoothTransition).continuous_deriv
      (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hd.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht0 : 0 ≤ t
  · by_cases ht1 : t ≤ 1
    · exact (hC t ⟨ht0, ht1⟩).trans (le_max_left _ _)
    · have hconst : HasDerivAt Real.smoothTransition (0 : ℝ) t := by
        apply (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
        filter_upwards [lt_mem_nhds (lt_of_not_ge ht1)] with r hr
        exact Real.smoothTransition.one_of_one_le hr.le
      rw [hconst.deriv, norm_zero]
      exact le_max_right _ _
  · have hconst : HasDerivAt Real.smoothTransition (0 : ℝ) t := by
      apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds (lt_of_not_ge ht0)] with r hr
      exact Real.smoothTransition.zero_of_nonpos hr.le
    rw [hconst.deriv, norm_zero]
    exact le_max_right _ _

private theorem smoothTransition_norm_le_one (t : ℝ) : ‖Real.smoothTransition t‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (Real.smoothTransition.nonneg t)]
  exact Real.smoothTransition.le_one t

private theorem cutoff_fderiv_bound_on_unitBall
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ B)
    (ε : ℝ) (hε : 0 < ε) (x : E) (hx : ‖x‖ ≤ 1) :
    ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x‖ ≤ 4 * B / ε := by
  let a : E → ℝ := fun y => (‖y‖ ^ 2 - ε) / ε
  let b : E → ℝ := fun y => (1 - ε - ‖y‖ ^ 2) / ε
  let L : E →L[ℝ] ℝ := ε⁻¹ • (2 • innerSL ℝ x)
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have ha : HasFDerivAt a L x := by
    simpa only [a, L, div_eq_mul_inv] using (hq.sub_const ε).mul_const ε⁻¹
  have hb : HasFDerivAt b (-L) x := by
    simpa only [b, L, div_eq_mul_inv, smul_neg] using (hq.const_sub (1 - ε)).mul_const ε⁻¹
  have hs (t : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).differentiable
      (by norm_num) t).hasDerivAt
  have hsa := (hs (a x)).comp_hasFDerivAt x ha
  have hsb := (hs (b x)).comp_hasFDerivAt x hb
  have hχ : HasFDerivAt (nativePuncturedUnitBallCutoff ε)
      (Real.smoothTransition (a x) • (deriv Real.smoothTransition (b x) • (-L)) +
        Real.smoothTransition (b x) • (deriv Real.smoothTransition (a x) • L)) x := by
    exact hsa.mul hsb
  have hLnorm : ‖L‖ = ε⁻¹ * (2 * ‖x‖) := by
    dsimp only [L]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le),
      RCLike.norm_nsmul ℝ, innerSL_apply_norm, two_nsmul, ← two_mul]
  have hL : ‖L‖ ≤ 2 / ε := by
    rw [hLnorm]
    calc
      _ ≤ ε⁻¹ * (2 * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2)) (inv_nonneg.mpr hε.le)
      _ = _ := by ring
  have hDa : ‖deriv Real.smoothTransition (a x) • L‖ ≤ B * (2 / ε) := by
    rw [norm_smul]
    exact mul_le_mul (hB _) hL (norm_nonneg _) hB0
  have hDb : ‖deriv Real.smoothTransition (b x) • (-L)‖ ≤ B * (2 / ε) := by
    rw [norm_smul, norm_neg]
    exact mul_le_mul (hB _) hL (norm_nonneg _) hB0
  have htermA : ‖Real.smoothTransition (a x) • (deriv Real.smoothTransition (b x) • (-L))‖ ≤
      ‖deriv Real.smoothTransition (b x) • (-L)‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (smoothTransition_norm_le_one _) (norm_nonneg _)).trans_eq
      (one_mul _)
  have htermB : ‖Real.smoothTransition (b x) • (deriv Real.smoothTransition (a x) • L)‖ ≤
      ‖deriv Real.smoothTransition (a x) • L‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (smoothTransition_norm_le_one _) (norm_nonneg _)).trans_eq
      (one_mul _)
  rw [hχ.fderiv]
  calc
    _ ≤ ‖Real.smoothTransition (a x) • (deriv Real.smoothTransition (b x) • (-L))‖ +
        ‖Real.smoothTransition (b x) • (deriv Real.smoothTransition (a x) • L)‖ := norm_add_le _ _
    _ ≤ ‖deriv Real.smoothTransition (b x) • (-L)‖ +
        ‖deriv Real.smoothTransition (a x) • L‖ := add_le_add htermA htermB
    _ ≤ B * (2 / ε) + B * (2 / ε) := add_le_add hDb hDa
    _ = _ := by ring

/-- One strictly positive constant is produced before epsilon and the
point.  The bound is global in space and holds for every positive
epsilon, in particular throughout the intended range `(0,1/4)`. -/
theorem exists_nativePuncturedUnitBallCutoff_gradient_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∀ x : E,
      ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x‖ ≤ K / ε := by
  obtain ⟨B, hB0, hB⟩ := smoothTransition_deriv_norm_bound
  refine ⟨4 * B + 1, by positivity, ?_⟩
  intro ε hε x
  have hbound : ‖fderiv ℝ (nativePuncturedUnitBallCutoff ε) x‖ ≤ 4 * B / ε := by
    by_cases hx : ‖x‖ ≤ 1
    · exact cutoff_fderiv_bound_on_unitBall B hB0 hB ε hε x hx
    · have hout : x ∉ tsupport (nativePuncturedUnitBallCutoff ε) := by
        intro hmem
        have hu := (nativePuncturedUnitBallCutoff_tsupport_annulus ε hε hmem).2
        have hx' : 1 < ‖x‖ := lt_of_not_ge hx
        nlinarith only [hu, hε, hx', sq_nonneg (‖x‖ - 1)]
      rw [fderiv_of_notMem_tsupport ℝ hout, norm_zero]
      exact div_nonneg (mul_nonneg (by norm_num) hB0) hε.le
  exact hbound.trans (div_le_div_of_nonneg_right (by linarith) hε.le)

#print axioms nativePuncturedUnitBallCutoff_contDiff
#print axioms nativePuncturedUnitBallCutoff_range
#print axioms nativePuncturedUnitBallCutoff_tsupport_annulus
#print axioms nativePuncturedUnitBallCutoff_tsupport_subset
#print axioms nativePuncturedUnitBallCutoff_hasCompactSupport
#print axioms nativePuncturedUnitBallCutoff_eq_one
#print axioms nativePuncturedUnitBallCutoff_fderiv_eq_zero
#print axioms nativePuncturedUnitBallCutoff_fderiv_tsupport_subset
#print axioms exists_nativePuncturedUnitBallCutoff_gradient_bound

end Yamabe3.Analysis.SpherePolar
