import Yamabe3.Analysis.NativeSupportedOuterFarEquation
import Yamabe3.Analysis.Green.UniformResidualJets
import Yamabe3.Analysis.NativeHalfEndH4Regularity

/-! The actual full-bubble spatial coefficient has uniform finite jets
in the far phase region. The phase parameter exp(alpha) is squared;
the compact parameter family is smooth even at its zero endpoint. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter Metric MeasureTheory PoincareMT
open scoped Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open Delaunay GreenParametrix UniformElliptic

def fullBubbleSpatialPotential (r:ℝ) (x:E) :ℝ :=
  15*r^2/(‖x‖^2+r^2)^2

theorem fullBubbleSpatialPotential_joint_smooth (q:ℝ×E) (hq:q.2≠0) :
    ContDiffAt ℝ ∞ (fun p:ℝ×E=>fullBubbleSpatialPotential p.1 p.2) q := by
  have hn:ContDiffAt ℝ ∞ (fun p:ℝ×E=>‖p.2‖) q:=
    (contDiffAt_norm ℝ hq).comp q contDiffAt_snd
  have hpos:0<‖q.2‖^2+q.1^2:=add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hq)) (sq_nonneg _)
  exact ((contDiffAt_const.mul (contDiffAt_fst.pow 2)).div
    (((hn.pow 2).add (contDiffAt_fst.pow 2)).pow 2) (pow_ne_zero 2 hpos.ne'))

theorem nativeHalfEnd_fullBubble_spatial_eq (α:ℝ) {x:E} (hx:x≠0) :
    nativeHalfEndPotentialCoefficient (fullBubblePhasePotential α) x=
      fullBubbleSpatialPotential (Real.exp α) x := by
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  have he0:Real.exp (-Real.log ‖x‖+α)=Real.exp α/‖x‖:=by
    rw [Real.exp_add,Real.exp_neg,Real.exp_log hn]
    ring
  have he:Real.exp (2*(-Real.log ‖x‖+α))=(Real.exp α)^2/‖x‖^2:=by
    calc
      _ = Real.exp (-Real.log ‖x‖+α)^2 := by rw [←Real.exp_nat_mul];norm_num
      _ = _ := by rw [he0,div_pow]
  change ((15/4:ℝ)*(4*Real.exp (2*(-Real.log ‖x‖+α))/(1+Real.exp (2*(-Real.log ‖x‖+α)))^2))/‖x‖^2=_
  rw [he]
  dsimp only [fullBubbleSpatialPotential]
  field_simp
  <;> ring

theorem exists_fullBubble_far_spatial_potential_jets (k:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀α:ℝ,α≤0→∀n≤k,∀x:E,(1/2:ℝ)≤‖x‖→‖x‖≤2→
      ‖iteratedFDeriv ℝ n (nativeHalfEndPotentialCoefficient (fullBubblePhasePotential α)) x‖≤C := by
  obtain ⟨C,hC,hb⟩:=exists_uniform_spatial_jet_bounds fullBubbleSpatialPotential_joint_smooth k
  refine ⟨C,hC,fun α hα n hn x hxlo hxhi=>?_⟩
  have hx:x≠0:=norm_pos_iff.mp (lt_of_lt_of_le (by norm_num:(0:ℝ)<1/2) hxlo)
  have he:nativeHalfEndPotentialCoefficient (fullBubblePhasePotential α)=ᶠ[𝓝 x]
      fullBubbleSpatialPotential (Real.exp α):=by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
    exact nativeHalfEnd_fullBubble_spatial_eq α hy
  rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
  exact hb n hn (Real.exp α) ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr hα⟩ x hxlo hxhi

#print axioms fullBubbleSpatialPotential_joint_smooth
#print axioms nativeHalfEnd_fullBubble_spatial_eq
#print axioms exists_fullBubble_far_spatial_potential_jets
end Yamabe3.Analysis.SpherePolar
