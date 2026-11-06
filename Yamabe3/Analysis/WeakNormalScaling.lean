import Yamabe3.Analysis.BoundaryNormalScaling

/-! Actual all-order weak Sobolev transport by normal-coordinate scaling.
The distributional change of variables retains the determinant and the
different normal/tangential derivative factors. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem map_restrict_volume_normalScaling {r : ℝ} (hr : r≠0) (O : Set E) :
    Measure.map (normalScaling r hr) (volume.restrict ((normalScaling r hr) ⁻¹' O))=
      ENNReal.ofReal |r⁻¹| • volume.restrict O := by
  have he : MeasurableEmbedding (normalScaling (d:=d) r hr) := (normalScaling r hr).toHomeomorph.measurableEmbedding
  rw [← he.restrict_map volume O,map_volume_normalScaling,Measure.restrict_smul]

theorem memLp_comp_normalScaling {r : ℝ} (hr : r≠0) {O : Set E}
    {u : E → ℝ} {p : ℝ≥0∞} (hu : MemLp u p (volume.restrict O)) :
    MemLp (fun x => u (normalScaling r hr x)) p (volume.restrict ((normalScaling r hr) ⁻¹' O)) := by
  have he : MeasurableEmbedding (normalScaling (d:=d) r hr) := (normalScaling r hr).toHomeomorph.measurableEmbedding
  change MemLp (u ∘ normalScaling r hr) p _
  rw [← he.memLp_map_measure_iff,map_restrict_volume_normalScaling hr]
  exact hu.smul_measure ENNReal.ofReal_ne_top

theorem setIntegral_comp_normalScaling {r : ℝ} (hr : r≠0) (O : Set E) (u : E → ℝ) :
    (∫ x in (normalScaling r hr) ⁻¹' O,u (normalScaling r hr x))=|r⁻¹| *(∫ x in O,u x) := by
  have he : MeasurableEmbedding (normalScaling (d:=d) r hr) := (normalScaling r hr).toHomeomorph.measurableEmbedding
  rw [← he.integral_map u,map_restrict_volume_normalScaling hr,integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul]

theorem hasWeakPartialDeriv_comp_normalScaling {r : ℝ} (hr : r≠0)
    {O : Set E} {u g : E → ℝ} {i : Fin d} (hw : HasWeakPartialDeriv i g u O) :
    HasWeakPartialDeriv i (fun x => normalFactor r i*g (normalScaling r hr x))
      (fun x => u (normalScaling r hr x)) ((normalScaling r hr) ⁻¹' O) := by
  intro φ hφ hc hs
  let N := normalScaling (d:=d) r hr
  let ψ := fun y => φ (N.symm y)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp N.symm.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph N.symm.toHomeomorph
  have hψs : tsupport ψ⊆O := by
    intro y hy
    have hpre := (tsupport_comp_eq_preimage φ N.symm.toHomeomorph).le hy
    have hh := hs hpre
    change N (N.symm y)∈O at hh
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have ht := hw ψ hψ hψc hψs
  have hval (x : E) : ψ (N x)=φ x := by simp only [ψ,ContinuousLinearEquiv.symm_apply_apply]
  have hder (x : E) : normalFactor r i*fderiv ℝ ψ (N x) (EuclideanSpace.single i 1)=
      fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    have hd := ((hφ.differentiable (by simp) (N.symm (N x))).hasFDerivAt.comp (N x)
      N.symm.toContinuousLinearMap.hasFDerivAt).fderiv
    change fderiv ℝ ψ (N x)=_ at hd
    rw [hd]
    have hsingle : N.symm (EuclideanSpace.single i 1)=normalFactor r⁻¹ i • EuclideanSpace.single i 1 :=
      normalScaling_single r⁻¹ (inv_ne_zero hr) i
    change normalFactor r i * fderiv ℝ φ (N.symm (N x)) (N.symm (EuclideanSpace.single i 1))=_
    rw [ContinuousLinearEquiv.symm_apply_apply,hsingle,map_smul,smul_eq_mul,← mul_assoc]
    have hfac : normalFactor r i*normalFactor r⁻¹ i=1 := by
      by_cases hi : i=0 <;> simp [normalFactor,hi,hr]
    rw [hfac,one_mul]
  calc
    _ = ∫ x in N ⁻¹' O,normalFactor r i*(u (N x)*fderiv ℝ ψ (N x) (EuclideanSpace.single i 1)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only;rw [mul_left_comm,hder]
    _ = normalFactor r i*(|r⁻¹| *(∫ y in O,u y*fderiv ℝ ψ y (EuclideanSpace.single i 1))) := by
      rw [integral_const_mul]
      dsimp only [N]
      rw [setIntegral_comp_normalScaling hr O (fun y => u y*fderiv ℝ ψ y (EuclideanSpace.single i 1))]
    _ = -(normalFactor r i*(|r⁻¹| *(∫ y in O,g y*ψ y))) := by rw [ht];ring
    _ = -(∫ x in N ⁻¹' O,normalFactor r i*(g (N x)*ψ (N x))) := by
      rw [integral_const_mul]
      dsimp only [N]
      rw [setIntegral_comp_normalScaling hr O (fun y => g y*ψ y)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only;rw [hval];ring

theorem memWkp_comp_normalScaling {r : ℝ} (hr : r≠0) {O : Set E}
    (hO : IsOpen O) {p : ℝ≥0∞} (hp : 1≤p) (k : ℕ) {u : E → ℝ}
    (hu : MemWkp k p u O) :
    MemWkp k p (fun x => u (normalScaling r hr x)) ((normalScaling r hr) ⁻¹' O) := by
  have hW : IsOpen ((normalScaling r hr) ⁻¹' O) := hO.preimage (normalScaling r hr).continuous
  induction k generalizing u with
  | zero => exact memLp_comp_normalScaling hr hu
  | succ k ih =>
    apply memWkp_succ_of_weakDerivatives hW hp (memLp_comp_normalScaling hr hu.memLp)
      (g:=fun i x => normalFactor r i*chosenWeakPartial' p i u O (normalScaling r hr x))
    · intro i
      exact MemWkp.const_smul hp hW (ih (hu.chosenWeakPartial_mem i)) (normalFactor r i)
    · intro i
      exact hasWeakPartialDeriv_comp_normalScaling hr (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)

#print axioms hasWeakPartialDeriv_comp_normalScaling
#print axioms memWkp_comp_normalScaling
end Yamabe3.Analysis.UniformElliptic
