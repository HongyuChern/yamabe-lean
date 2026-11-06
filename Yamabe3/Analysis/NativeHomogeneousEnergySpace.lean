import Yamabe3.Analysis.NativeCriticalSourceFreeRepresentative

/-! An actual complete working space for native local-homogeneous
energy fields, defined by the weak equation against genuine supported
energy tests. Its regular representative is constructed from that equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def homogeneousEnergyH1Normed (g : RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ) := inferInstance
attribute [local instance] homogeneousEnergyH1Normed

def nativeHomogeneousEnergySpace (g : RiemannianMetric 3 M) (B : M → ℝ)
    (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) (Ω : Set M) :
    Submodule ℝ (H1Zero g.leviCivitaData univ) where
  carrier := {W | ∀φ : EnergyTest g.leviCivitaData univ, tsupport (φ : M → ℝ) ⊆ Ω →
    closedYamabeJacobianForm g B hB W (φ : H1Zero g.leviCivitaData univ)=0}
  zero_mem' := by intro φ hs;rw [map_zero,ContinuousLinearMap.zero_apply]
  add_mem' := by
    intro W Z hW hZ φ hs
    rw [map_add,ContinuousLinearMap.add_apply,hW φ hs,hZ φ hs,add_zero]
  smul_mem' := by
    intro c W hW φ hs
    rw [map_smul,ContinuousLinearMap.smul_apply,hW φ hs,smul_zero]

instance nativeHomogeneousEnergySpace_closed (g : RiemannianMetric 3 M) (B : M → ℝ)
    (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) (Ω : Set M) :
    IsClosed (nativeHomogeneousEnergySpace g B hB Ω : Set (H1Zero g.leviCivitaData univ)) := by
  change IsClosed {W : H1Zero g.leviCivitaData univ | ∀φ : EnergyTest g.leviCivitaData univ,
    tsupport (φ : M → ℝ) ⊆ Ω → closedYamabeJacobianForm g B hB W (φ : H1Zero g.leviCivitaData univ)=0}
  simp only [setOf_forall]
  exact isClosed_iInter fun φ => isClosed_iInter fun hs => isClosed_eq (by fun_prop) continuous_const

theorem nativeHomogeneousEnergySpace_complete (g : RiemannianMetric 3 M) (B : M → ℝ)
    (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B) (Ω : Set M) :
    CompleteSpace (nativeHomogeneousEnergySpace g B hB Ω) := inferInstance

theorem nativeHomogeneousEnergySpace_of_global_equation
    (g : RiemannianMetric 3 M) (B : M → ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Ω : Set M) (W : H1Zero g.leviCivitaData univ) (F : M → ℝ)
    (hw : ∀η : H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g B hB W η=
      ∫x,F x*toL2 g.leviCivitaData univ η x ∂g.volumeMeasure)
    (hF : ∀x∈Ω,F x=0) : W∈nativeHomogeneousEnergySpace g B hB Ω := by
  intro φ hs
  rw [hw,toL2_coe]
  apply integral_eq_zero_of_ae
  filter_upwards [φ.memLp.coeFn_toLp] with x hx
  change F x*testToL2 g.leviCivitaData univ φ x=0
  rw [show testToL2 g.leviCivitaData univ φ x=φ x from hx]
  by_cases h : x∈Ω
  · rw [hF x h,zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => h (hs ht)),mul_zero]

theorem exists_nativeHomogeneousEnergy_smooth_representative
    (g : RiemannianMetric 3 M) (B : M → ℝ) (hB : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {Ω : Set M} (hΩ : IsOpen Ω) (W : nativeHomogeneousEnergySpace g B hB Ω) :
    ∃U : M → ℝ, ContMDiffOn (𝓡 3) 𝓘(ℝ,ℝ) ∞ U Ω ∧
      U=ᵐ[g.volumeMeasure.restrict Ω](toL2 g.leviCivitaData univ W.val : M → ℝ) ∧
      ∀x∈Ω,-8*g.leviCivitaData.laplacian U x+
        (g.leviCivitaData.scalarCurvature x-30*B x^4)*U x=0 := by
  let V := fun x : M => (g.leviCivitaData.scalarCurvature x-30*B x^4)/8
  have hV : ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V :=
    (g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul (hB.pow 4))).div_const 8
  have hweak : ∀φ : EnergyTest g.leviCivitaData univ, tsupport (φ : M → ℝ) ⊆ Ω →
      (∫x,(-g.leviCivitaData.laplacian φ x+V x*φ x)*toL2 g.leviCivitaData univ W.val x ∂g.volumeMeasure)=
        ∫x,φ x*(0 : ℝ) ∂g.volumeMeasure := by
    intro φ hs
    have hh := W.property φ hs
    rw [closedYamabeJacobianForm_test_eq_integral] at hh
    calc
      _ = (1/8 : ℝ)*(∫x,(-8*g.leviCivitaData.laplacian φ x+
        g.leviCivitaData.scalarCurvature x*φ x-30*B x^4*φ x)*toL2 g.leviCivitaData univ W.val x ∂g.volumeMeasure) := by
        rw [← integral_const_mul]
        congr 1
        funext x
        dsimp only [V]
        ring
      _ = _ := by rw [hh];simp
  obtain ⟨U,hU,hUAE,hP⟩ := exists_native_smooth_representative_of_locally_smooth_forcing
    (by norm_num : 0 < 3) hΩ V (fun _ : M => 0) hV contMDiffOn_const W.val hweak
  refine ⟨U,hU,hUAE,fun x hx => ?_⟩
  have hh := hP x hx
  dsimp only [V] at hh
  linarith only [hh]

#print axioms nativeHomogeneousEnergySpace_complete
#print axioms nativeHomogeneousEnergySpace_of_global_equation
#print axioms exists_nativeHomogeneousEnergy_smooth_representative
end Yamabe3.Analysis.SpherePolar
