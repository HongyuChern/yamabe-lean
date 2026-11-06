import Yamabe3.Analysis.NativePrincipalErrorGraph
import Yamabe3.Analysis.UniformElliptic.RegularFieldSourceGraphCost

/-! The four regular low jets are retained alongside a decaying H4
correction. The actual native principal error of their affine field is
an arbitrarily small operator into the ORIGINAL weighted H2 source graph.
The divergence drift, not an assumed vanishing low component, is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Set Filter Metric MeasureTheory PoincareMT
open scoped ContDiff Topology ENNReal BigOperators
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar Poincare.Analysis.Elliptic.Iteration
local notation "E3" => EuclideanSpace ℝ (Fin 3)
abbrev RegularLowJet := ℝ × (E3 →L[ℝ] ℝ)

def regularAffineField (z : RegularLowJet) (x:E3) : ℝ := z.1+z.2 x

theorem regularAffineField_smooth (z:RegularLowJet) : ContDiff ℝ ∞ (regularAffineField z) :=
  contDiff_const.add z.2.contDiff

theorem regularAffineField_partial (z:RegularLowJet) (j:Fin 3) (x:E3) :
    partialDeriv j (regularAffineField z) x=z.2 (EuclideanSpace.single j 1) := by
  unfold partialDeriv regularAffineField
  rw [fderiv_const_add]
  · rw [z.2.fderiv]

def nativeAffineDriftLinear (g:RiemannianMetric 3 E3) (ε:ℝ) : RegularLowJet →ₗ[ℝ] (E3→ℝ) where
  toFun z x := ∑j:Fin 3,nativeScaledFirstError g ε j x*z.2 (EuclideanSpace.single j 1)
  map_add' z w := by funext x;simp only [Prod.fst_add,Prod.snd_add,ContinuousLinearMap.add_apply,mul_add,Finset.sum_add_distrib,Pi.add_apply]
  map_smul' c z := by
    funext x
    change (∑j:Fin 3,nativeScaledFirstError g ε j x*(c • z.2) (EuclideanSpace.single j 1))=
      c*(∑j:Fin 3,nativeScaledFirstError g ε j x*z.2 (EuclideanSpace.single j 1))
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)

theorem nativeAffineDrift_eq_principal (g:RiemannianMetric 3 E3) (ε:ℝ) (z:RegularLowJet) (x:E3) :
    nativeAffineDriftLinear g ε z x=nativePrincipalError g ε (regularAffineField z) x := by
  rw [nativePrincipalError_eq_classical g ε ((regularAffineField_smooth z).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  dsimp only [nativeScaledGeometricError,secondOrderPerturbation,nativeAffineDriftLinear,LinearMap.coe_mk,AddHom.coe_mk]
  have hp (j:Fin 3) : partialDeriv j (regularAffineField z)=(fun _ => z.2 (EuclideanSpace.single j 1)) :=
    funext (regularAffineField_partial z j)
  have hpp (i j:Fin 3) : partialDeriv i (partialDeriv j (regularAffineField z)) x=0 := by
    rw [hp]
    simp [partialDeriv]
  simp only [regularAffineField_partial,hpp,mul_zero,Finset.sum_const_zero,zero_mul,zero_add,add_zero]

theorem nativeAffineDrift_smooth (g:RiemannianMetric 3 E3) (ε:ℝ) (z:RegularLowJet) :
    ContDiff ℝ ∞ (nativeAffineDriftLinear g ε z) :=
  by
    change ContDiff ℝ ∞ (fun x => ∑j:Fin 3,nativeScaledFirstError g ε j x*z.2 (EuclideanSpace.single j 1))
    exact ContDiff.sum fun j _ => (contDiff_nativeScaledFirstError g ε j).mul contDiff_const

theorem nativeAffineDrift_two_jets (g:RiemannianMetric 3 E3) (ε:ℝ) {η:ℝ} (hη:0≤η)
    (hb:∀n≤2,∀x∈closedBall (0:E3) 4,∀j:Fin 3,‖iteratedFDeriv ℝ n (nativeScaledFirstError g ε j) x‖≤η) :
    ∀z:RegularLowJet,∀n≤2,∀x∈closedBall (0:E3) 4,
      ‖iteratedFDeriv ℝ n (nativeAffineDriftLinear g ε z) x‖≤(3*η)*‖z‖ := by
  intro z n hn x hx
  change ‖iteratedFDeriv ℝ n (fun y => ∑j:Fin 3,nativeScaledFirstError g ε j y*z.2 (EuclideanSpace.single j 1)) x‖≤_
  rw [iteratedFDeriv_fun_sum_apply]
  · apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑_j:Fin 3,η*‖z‖ := by
        apply Finset.sum_le_sum
        intro j _
        have he : (fun y => nativeScaledFirstError g ε j y*z.2 (EuclideanSpace.single j 1))=
            fun y => z.2 (EuclideanSpace.single j 1) • nativeScaledFirstError g ε j y := by funext y;simp [smul_eq_mul,mul_comm]
        rw [he,iteratedFDeriv_const_smul_apply',norm_smul]
        · have hz : ‖z.2 (EuclideanSpace.single j 1)‖≤‖z‖ :=
            (z.2.le_opNorm _).trans (by
              have he : ‖(EuclideanSpace.single j (1:ℝ):E3)‖=1 := by simp
              rw [he,mul_one]
              exact norm_snd_le z)
          exact (mul_le_mul hz (hb n hn x hx j) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
        · exact (contDiff_nativeScaledFirstError g ε j).contDiffAt.of_le (by exact_mod_cast le_top)
      _ = _ := by simp;ring
  · intro j _
    exact ((contDiff_nativeScaledFirstError g ε j).mul contDiff_const).contDiffAt.of_le (by exact_mod_cast le_top)

theorem exists_small_native_affine_principal_source
    {ι:Type*} (Λ:Finset ι) (g:ι→RiemannianMetric 3 E3)
    (hB:∀p∈Λ,(g p).euclideanCoefficients 0=innerSL ℝ)
    (hρ:∀p∈Λ,(g p).pullbackVolumeDensity id 0=1) {τ:ℝ} (hτ:0<τ) :
    ∃δ:ℝ,0<δ ∧ ∀ε:ℝ,0≤ε → ε<δ → ∀p∈Λ,
      ∃T:RegularLowJet →L[ℝ] HalfEndPhysicalH2SourceGraph,‖T‖≤τ ∧
        ∀z:RegularLowJet,∀x:HalfEndSourceEntrance,
          halfEndPhysicalH2SourceGraphValue (T z) x=
            nativeNormalizedPrincipalError (g p) ε (regularAffineField z) x := by
  let η := τ/(3*(regularFieldSourceGraphCost+1))
  have hη : 0<η := by dsimp only [η];positivity [regularFieldSourceGraphCost_nonneg]
  obtain ⟨δ,hδ,hsmall⟩ := exists_uniform_small_native_geometric_error Λ g hB hρ
    (by norm_num:(0:ℝ)<4) (show 0<91*η by positivity)
  refine ⟨δ,hδ,fun ε hε hεδ p hp => ?_⟩
  have hcoeff : ∀n≤2,∀x∈closedBall (0:E3) 4,∀j:Fin 3,
      ‖iteratedFDeriv ℝ n (nativeScaledFirstError (g p) ε j) x‖≤η := by
    intro n hn x hx j
    simpa only [show (91:ℝ)*η/91=η by ring] using (hsmall ε hε hεδ p hp).2.1 n hn x hx j
  obtain ⟨T,hT,hTv⟩ := exists_regularField_source_graph_with_cost (nativeAffineDriftLinear (g p) ε)
    (fun z => (nativeAffineDrift_smooth _ _ z).contDiffOn) (3*η) (by positivity)
    (nativeAffineDrift_two_jets _ _ hη.le hcoeff)
  refine ⟨T,hT.trans ?_,fun z x => ?_⟩
  · have hc := regularFieldSourceGraphCost_nonneg
    have hd : 0<3*(regularFieldSourceGraphCost+1) := by positivity
    dsimp only [η]
    have hp : 0<regularFieldSourceGraphCost+1 := by positivity
    calc
      _ = τ*(regularFieldSourceGraphCost/(regularFieldSourceGraphCost+1)) := by field_simp <;> ring
      _ ≤ τ*1 := mul_le_mul_of_nonneg_left ((div_le_one hp).mpr (by linarith)) hτ.le
      _ = τ := mul_one _
  · rw [hTv]
    unfold regularFieldSourceValue
    rw [nativeAffineDrift_eq_principal]
    unfold nativeNormalizedPrincipalError
    ring

#print axioms regularAffineField_partial
#print axioms nativeAffineDrift_eq_principal
#print axioms nativeAffineDrift_two_jets
#print axioms exists_small_native_affine_principal_source
end Yamabe3.Analysis.UniformElliptic
