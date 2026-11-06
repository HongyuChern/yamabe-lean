import Yamabe3.Analysis.NativeH4GraphAllScaleJet
import Yamabe3.Analysis.NativeRegularH4PrincipalError
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! One regular-low-plus-H4 field supplies its actual full collar jet.
The affine low coordinates are genuine and retained; finite-dimensional
continuity is used only for their explicit fixed-scale linear map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Topology ContDiff ENNReal
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar Delaunay

private def affineDilatedLinear (s:ℝ) : RegularLowJet →ₗ[ℝ] nativeC2OffZero where
  toFun z:=⟨fun x:E=>Real.exp (3*s/2)*regularAffineField z (Real.exp (-s) • x),by
    have hh:ContDiff ℝ ∞ (fun x:E=>Real.exp (3*s/2)*regularAffineField z (Real.exp (-s) • x)) :=
      (contDiff_const (c:=Real.exp (3*s/2))).mul ((regularAffineField_smooth z).comp (contDiff_id.const_smul (Real.exp (-s))))
    exact (hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn⟩
  map_add' z w:=by
    apply Subtype.ext
    funext x
    change Real.exp (3*s/2)*(regularAffineField (z+w) (Real.exp (-s) • x))=
      Real.exp (3*s/2)*regularAffineField z (Real.exp (-s) • x)+Real.exp (3*s/2)*regularAffineField w (Real.exp (-s) • x)
    simp only [regularAffineField,Prod.fst_add,Prod.snd_add,ContinuousLinearMap.add_apply]
    ring
  map_smul' c z:=by
    simp only [RingHom.id_apply]
    apply Subtype.ext
    funext x
    change Real.exp (3*s/2)*regularAffineField (c • z) (Real.exp (-s) • x)=
      c*(Real.exp (3*s/2)*regularAffineField z (Real.exp (-s) • x))
    change Real.exp (3*s/2)*(c*z.1+c*z.2 (Real.exp (-s) • x))=
      c*(Real.exp (3*s/2)*(z.1+z.2 (Real.exp (-s) • x)))
    ring

def regularAffineScaleJetCLM (s:ℝ) : RegularLowJet →L[ℝ] nativeCollarJetClosure :=
  ⟨nativeC2CollarJetInclusion.comp (affineDilatedLinear s),
    (nativeC2CollarJetInclusion.comp (affineDilatedLinear s)).continuous_of_finiteDimensional⟩

theorem regularAffineScaleJet_value (s:ℝ) (z:RegularLowJet) :
    ((regularAffineScaleJetCLM s z).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun x:E=>Real.exp (3*s/2)*regularAffineField z (Real.exp (-s) • x) :=
  (nativeC2Collar_memLp (affineDilatedLinear s z).property).1.coeFn_toLp

def regularLowH4ScaleJetCLM (i:HalfEndPhysicalSliceIndex) : RegularLowH4Space →L[ℝ] nativeCollarJetClosure :=
  (regularAffineScaleJetCLM i.1).comp (ContinuousLinearMap.fst ℝ RegularLowJet HalfEndPhysicalH4Graph)+
    (nativeH4GraphScaleJetCLM i).comp (ContinuousLinearMap.snd ℝ RegularLowJet HalfEndPhysicalH4Graph)

theorem regularLowH4ScaleJet_value (i:HalfEndPhysicalSliceIndex) (z:RegularLowH4Space) :
    ((regularLowH4ScaleJetCLM i z).val.1:E→ℝ)=ᵐ[volume.restrict nativePoissonEntranceCollar]
      fun x:E=>Real.exp (3*i.1/2)*regularLowH4Field z (Real.exp (-i.1) • x) := by
  have hv:=nativeH4GraphScaleJet_same_function i z.2
    (halfEndEntranceExtension (halfEndPhysicalH4GraphValue z.2)) (fun _ _=>rfl)
  have ha:=regularAffineScaleJet_value i.1 z.1
  filter_upwards [hv,ha,Lp.coeFn_add (regularAffineScaleJetCLM i.1 z.1).val.1
    (nativeH4GraphScaleJetCLM i z.2).val.1] with x hv ha hsum
  change ((regularAffineScaleJetCLM i.1 z.1).val.1+(nativeH4GraphScaleJetCLM i z.2).val.1:NativeCollarL2) x=_
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hv,ha]
  unfold regularLowH4Field
  ring

theorem regularLowH4ScaleJet_norm (i:HalfEndPhysicalSliceIndex) :
    ‖regularLowH4ScaleJetCLM i‖ ≤ ‖regularAffineScaleJetCLM i.1‖+1 := by
  apply (regularLowH4ScaleJetCLM i).opNorm_le_bound (by positivity)
  intro z
  change ‖regularAffineScaleJetCLM i.1 z.1+nativeH4GraphScaleJetCLM i z.2‖ ≤ _
  apply (norm_add_le _ _).trans
  have ha:‖regularAffineScaleJetCLM i.1 z.1‖ ≤ ‖regularAffineScaleJetCLM i.1‖*‖z‖ :=
    ((regularAffineScaleJetCLM i.1).le_opNorm z.1).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg _))
  have hb:‖nativeH4GraphScaleJetCLM i z.2‖ ≤ ‖z‖ :=
    (nativeH4GraphScaleJet_norm i z.2).trans (norm_snd_le z)
  exact (add_le_add ha hb).trans_eq (by ring)

#print axioms regularAffineScaleJet_value
#print axioms regularLowH4ScaleJet_value
#print axioms regularLowH4ScaleJet_norm
end Yamabe3.Analysis.UniformElliptic
