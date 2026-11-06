import Yamabe3.Analysis.NativeHighDtN

/-!
A two-sided inverse on the same genuine high angular H1/L2 spaces. Each
operator is the actual normal derivative constructed in NativeHighDtN.
The reciprocal sum is synthesized in the native energy basis. Potential
admissibility is input data here; bubble and orbit instances are separate
proof obligations and are not asserted by the bundle below.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

structure NativeHighPotential where
  κ : ℝ
  κ_nonneg : 0 ≤ κ
  κ_lt_one : κ < 1
  potential : ℝ →ᵇ ℝ
  kernel_bound : ∀ t, (∫ s : ℝ, spectralMajorant (5/2) (-2) s * |potential (t-s)|) ≤ κ
  nonneg : ∀ t, 0 ≤ potential t
  upper : ∀ t : ℝ, 0 ≤ t → potential t ≤ 15/4

namespace NativeHighPotential

def dtn (P : NativeHighPotential) : AngularH1 →L[ℝ] AngularL2 :=
  nativeHighDtN P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg

def symbol (P : NativeHighPotential) (i : AngularIndex) : ℝ :=
  nativeHighDtNSymbol P.κ_nonneg P.κ_lt_one P.potential P.kernel_bound P.nonneg i

theorem coefficient (P : NativeHighPotential) (b : AngularH1) (i : AngularIndex) :
    inner ℝ (angularBasis i) (P.dtn b) =
      if 6 ≤ angularEigenvalue i then P.symbol i * inner ℝ (angularBasis i) (angularEmbedding b)
      else 0 := nativeHighDtN_coefficient _ _ _ _ _ _ _

theorem symbol_lower (P : NativeHighPotential) (i : AngularIndex) (hi : 6 ≤ angularEigenvalue i) :
    angularEnergyWeight i / 4 + 1/2 ≤ P.symbol i :=
  nativeHighDtNSymbol_lower _ _ _ _ _ P.upper i hi

theorem high (P : NativeHighPotential) (b : AngularH1) :
    nativeHighProjection (P.dtn b) = P.dtn b := nativeHighDtN_high _ _ _ _ _ b

end NativeHighPotential

variable (B W : NativeHighPotential)

private theorem symbol_sum_pos (i : AngularIndex) (hi : 6 ≤ angularEigenvalue i) :
    0 < B.symbol i + W.symbol i := by
  have hB := B.symbol_lower i hi
  have hW := W.symbol_lower i hi
  have hp := angularEnergyWeight_pos i
  linarith

private def inverseWeight (i : AngularIndex) : ℝ :=
  if 6 ≤ angularEigenvalue i then angularEnergyWeight i / (B.symbol i + W.symbol i) else 0

private theorem inverseWeight_bound (i : AngularIndex) : |inverseWeight B W i| ≤ 2 := by
  unfold inverseWeight
  split_ifs with hi
  · rw [abs_of_pos (div_pos (angularEnergyWeight_pos i) (symbol_sum_pos B W i hi)),
      div_le_iff₀ (symbol_sum_pos B W i hi)]
    linarith only [B.symbol_lower i hi, W.symbol_lower i hi]
  · norm_num

/-- Actual bounded inverse of the sum, extended by zero on low data. -/
def nativeHighCoupledDtNInverse : AngularL2 →L[ℝ] AngularH1 :=
  angularEnergyBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((spectralDiagonal (inverseWeight B W) (by norm_num : (0:ℝ) ≤ 2)
      (inverseWeight_bound B W)).comp angularBasis.repr.toLinearIsometry.toContinuousLinearMap)

theorem nativeHighCoupledDtNInverse_coefficient (f : AngularL2) (i : AngularIndex) :
    inner ℝ (angularBasis i) (angularEmbedding (nativeHighCoupledDtNInverse B W f)) =
      if 6 ≤ angularEigenvalue i then
        inner ℝ (angularBasis i) f / (B.symbol i + W.symbol i) else 0 := by
  have h := (angularEnergyBasis_synthesis_spec
    (spectralDiagonal (inverseWeight B W) (by norm_num : (0:ℝ) ≤ 2)
      (inverseWeight_bound B W) (angularBasis.repr f))).1 i
  change inner ℝ (angularBasis i) (angularEmbedding (nativeHighCoupledDtNInverse B W f)) = _ at h
  rw [spectralDiagonal_apply, HilbertBasis.repr_apply_apply] at h
  rw [h]
  unfold inverseWeight
  split_ifs with hi
  · field_simp [(angularEnergyWeight_pos i).ne']
  · simp

/-- Both sides use the same native high L2 projection. -/
theorem nativeHighCoupledDtNInverse_right (f : AngularL2) :
    (B.dtn + W.dtn) (nativeHighCoupledDtNInverse B W f) = nativeHighProjection f := by
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply, ContinuousLinearMap.add_apply, inner_add_right]
  rw [B.coefficient, W.coefficient, nativeHighCoupledDtNInverse_coefficient,
    nativeHighProjection, nativeAngularProjection_coefficient]
  split_ifs with hi
  · field_simp [(symbol_sum_pos B W i hi).ne']
    <;> ring
  · simp

/-- The left inverse identity retains the genuine high H1 projection. -/
theorem nativeHighCoupledDtNInverse_left (b : AngularH1) :
    nativeHighCoupledDtNInverse B W ((B.dtn + W.dtn) b) = nativeHighEnergyProjectionCLM b := by
  apply angularEmbedding_injective
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighCoupledDtNInverse_coefficient, nativeHighEnergyProjectionCLM_embedding,
    nativeHighProjection, nativeAngularProjection_coefficient,
    ContinuousLinearMap.add_apply, inner_add_right, B.coefficient, W.coefficient]
  split_ifs with hi
  · field_simp [(symbol_sum_pos B W i hi).ne']
    <;> ring
  · rfl

theorem nativeHighCoupledDtNInverse_high (f : AngularL2) :
    nativeHighEnergyProjectionCLM (nativeHighCoupledDtNInverse B W f) =
      nativeHighCoupledDtNInverse B W f := by
  apply angularEmbedding_injective
  apply angularBasis.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  rw [nativeHighEnergyProjectionCLM_embedding, nativeHighProjection,
    nativeAngularProjection_coefficient, nativeHighCoupledDtNInverse_coefficient]
  split_ifs <;> rfl

theorem nativeHighCoupledDtNInverse_norm (f : AngularL2) :
    ‖nativeHighCoupledDtNInverse B W f‖ ≤ 2 * ‖f‖ := by
  change ‖angularEnergyBasis.repr.symm
    (spectralDiagonal (inverseWeight B W) (by norm_num : (0:ℝ) ≤ 2)
      (inverseWeight_bound B W) (angularBasis.repr f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  simpa only [LinearIsometryEquiv.norm_map] using mul_le_mul_of_nonneg_right
    (spectralDiagonal_norm_le _ (by norm_num : (0:ℝ) ≤ 2) (inverseWeight_bound B W))
    (norm_nonneg (angularBasis.repr f))

/-- Existence and uniqueness, with the witness preceding the equation,
for every actual high normal datum. No inverse is supplied as input. -/
theorem exists_unique_nativeHighCoupledDtN_solution
    (f : AngularL2) (hf : nativeHighProjection f = f) :
    ∃! b : AngularH1, nativeHighEnergyProjectionCLM b = b ∧ (B.dtn + W.dtn) b = f := by
  refine ⟨nativeHighCoupledDtNInverse B W f,
    ⟨nativeHighCoupledDtNInverse_high B W f, ?_⟩, ?_⟩
  · rw [nativeHighCoupledDtNInverse_right, hf]
  · intro b hb
    have h := congrArg (nativeHighCoupledDtNInverse B W) hb.2
    rw [nativeHighCoupledDtNInverse_left, hb.1] at h
    exact h

/-- The two actual normal operators solve the simultaneous high value
and derivative jump equations with one boundary correction. -/
theorem exists_nativeHighCoupled_cauchy_matching
    (d : AngularH1) (hd : nativeHighEnergyProjectionCLM d = d)
    (n : AngularL2) (hn : nativeHighProjection n = n) :
    ∃ σ : AngularH1, nativeHighEnergyProjectionCLM σ = σ ∧
      nativeHighEnergyProjectionCLM (σ+d) = σ+d ∧
      (σ+d) - σ = d ∧ B.dtn (σ+d) + W.dtn σ = n := by
  let f := n - B.dtn d
  have hf : nativeHighProjection f = f := by rw [map_sub, hn, B.high]
  let σ := nativeHighCoupledDtNInverse B W f
  have hs : nativeHighEnergyProjectionCLM σ = σ := nativeHighCoupledDtNInverse_high B W f
  have he : (B.dtn + W.dtn) σ = f := by rw [nativeHighCoupledDtNInverse_right, hf]
  refine ⟨σ, hs, by rw [map_add, hs, hd], by abel, ?_⟩
  rw [map_add]
  change B.dtn σ + W.dtn σ = n - B.dtn d at he
  exact (show B.dtn σ + B.dtn d + W.dtn σ = (B.dtn σ + W.dtn σ) + B.dtn d by abel).trans
    (by rw [he]; abel)

#print axioms nativeHighCoupledDtNInverse
#print axioms nativeHighCoupledDtNInverse_right
#print axioms nativeHighCoupledDtNInverse_left
#print axioms exists_unique_nativeHighCoupledDtN_solution
#print axioms exists_nativeHighCoupled_cauchy_matching
end Yamabe3.Analysis.Delaunay
