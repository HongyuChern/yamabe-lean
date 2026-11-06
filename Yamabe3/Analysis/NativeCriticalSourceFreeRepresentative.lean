import Yamabe3.Analysis.NativeChartCriticalSolution
import Yamabe3.Analysis.NativeLocallySmoothForcing

/-! The actual completed critical solution has a genuine smooth
homogeneous representative on a source-free open set, with the same
native L2 class. This supplies the field needed by returning estimates. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem exists_nativeCritical_sourceFree_representative
    (g:RiemannianMetric 3 M) (b:M→ℝ) (hb:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
    (w:H1Zero g.leviCivitaData univ) (F:M→ℝ)
    (hw:∀η:H1Zero g.leviCivitaData univ,
      closedYamabeJacobianForm g b hb w η=
        ∫x,F x*toL2 g.leviCivitaData univ η x ∂g.volumeMeasure)
    {Ω:Set M} (hΩ:IsOpen Ω) (hF:∀x∈Ω,F x=0) :
    ∃U:M→ℝ,ContMDiffOn (𝓡 3) 𝓘(ℝ,ℝ) ∞ U Ω ∧
      U=ᵐ[g.volumeMeasure.restrict Ω](toL2 g.leviCivitaData univ w:M→ℝ) ∧
      ∀x∈Ω,-8*g.leviCivitaData.laplacian U x+
        (g.leviCivitaData.scalarCurvature x-30*b x^4)*U x=0 := by
  let V:=fun x:M=>(g.leviCivitaData.scalarCurvature x-30*b x^4)/8
  have hV:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V:=
    (g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul (hb.pow 4))).div_const 8
  have hweak:∀φ:EnergyTest g.leviCivitaData univ,tsupport (φ:M→ℝ)⊆Ω→
      (∫x,(-g.leviCivitaData.laplacian φ x+V x*φ x)*toL2 g.leviCivitaData univ w x ∂g.volumeMeasure)=
        ∫x,φ x*(0:ℝ) ∂g.volumeMeasure:=by
    intro φ hs
    have hh:=hw (φ:H1Zero g.leviCivitaData univ)
    rw [closedYamabeJacobianForm_test_eq_integral,toL2_coe] at hh
    have hz:(∫x,F x*testToL2 g.leviCivitaData univ φ x ∂g.volumeMeasure)=0:=by
      have hae:∀ᵐx ∂g.volumeMeasure,F x*testToL2 g.leviCivitaData univ φ x=0:=by
        filter_upwards [φ.memLp.coeFn_toLp] with x hx
        change F x*testToL2 g.leviCivitaData univ φ x=0
        rw [show testToL2 g.leviCivitaData univ φ x=φ x from hx]
        by_cases h:x∈Ω
        · rw [hF x h,zero_mul]
        · rw [image_eq_zero_of_notMem_tsupport (fun ht=>h (hs ht)),mul_zero]
      exact integral_eq_zero_of_ae hae
    rw [hz] at hh
    calc
      _ = (1/8:ℝ)*(∫x,(-8*g.leviCivitaData.laplacian φ x+
          g.leviCivitaData.scalarCurvature x*φ x-30*b x^4*φ x)*
            toL2 g.leviCivitaData univ w x ∂g.volumeMeasure):=by
        rw [←integral_const_mul]
        congr 1
        funext x
        dsimp only [V]
        ring
      _ = _:=by rw [hh];simp
  obtain ⟨U,hU,hUae,heq⟩:=exists_native_smooth_representative_of_locally_smooth_forcing
    (by norm_num:0<3) hΩ V (fun _:M=>0) hV contMDiffOn_const w hweak
  refine ⟨U,hU,hUae,fun x hx=>?_⟩
  have h:=heq x hx
  dsimp only [V] at h
  linarith only [h]

#print axioms exists_nativeCritical_sourceFree_representative
end Yamabe3.Analysis.SpherePolar
