import Yamabe3.Analysis.NativeAngularC2Spectral
import Mathlib.Analysis.Normed.Operator.Banach

/-! A proved spectral membership upgrade of an actual bounded angular map.
The weighted coefficient map has a closed graph, since each coefficient
is continuous. Banach closed graph supplies one uniform bound, preceding
all inputs. Membership is an obligation to be discharged for the original
H4 graph, not a new hypothesis on the final source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open SphereSpectrum

theorem nativeAngularSpectral_uniform_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X →L[ℝ] AngularL2) (s : ℝ)
    (h : ∀x,NativeAngularSpectralRegular s (T x)) :
    ∃C : ℝ,0≤C ∧ ∀x,(∑'i,nativeAngularWeightedSquare s (T x) i)≤C*‖x‖^2 := by
  let c (x : X) (i : AngularIndex) := (angularEnergyWeight i)^s*inner ℝ (angularBasis i) (T x)
  have hc (x : X) : Memℓp (c x) 2 := by
    have hs : Summable (fun i => (c x i)^2) := h x
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hs
  let L : X →ₗ[ℝ] SpectralSpace AngularIndex :=
    {toFun := fun x => ⟨c x,hc x⟩
     map_add' := by
       intro x y
       ext i
       simp only [c,map_add,inner_add_right,mul_add,lp.coeFn_add,Pi.add_apply]
     map_smul' := by
       intro a x
       ext i
       simp only [c,map_smul,inner_smul_right,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
       ring}
  have hL : Continuous L := by
    apply L.continuous_of_seq_closed_graph
    intro u x y hu hy
    ext i
    have h1 := ((lp.evalCLM ℝ (fun _ : AngularIndex => ℝ) 2 i).continuous.tendsto y).comp hy
    have hcont : Continuous (fun x : X => c x i) := by dsimp only [c];fun_prop
    have h2 := hcont.tendsto x |>.comp hu
    exact tendsto_nhds_unique h1 h2
  let S : X →L[ℝ] SpectralSpace AngularIndex := ⟨L,hL⟩
  refine ⟨‖S‖^2,sq_nonneg _,fun x => ?_⟩
  have he : ‖S x‖^2=∑'i,nativeAngularWeightedSquare s (T x) i := by
    have hn := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (S x)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] at hn
    exact hn
  rw [←he,←mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm x) 2

#print axioms nativeAngularSpectral_uniform_bound
end Yamabe3.Analysis.Delaunay
