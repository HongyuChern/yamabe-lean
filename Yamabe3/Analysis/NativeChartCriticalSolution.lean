import Yamabe3.Analysis.NativeChartCriticalTransport

/-! The genuine compact critical source is fed to the existing closed
inverse, retaining its native weak equation and norm. This is the small
smooth background operator, not the full bubble exterior operator. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Manifold ContDiff Topology ENNReal
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
private def chartCriticalH1Normed (g:RiemannianMetric 3 M):
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] chartCriticalH1Normed
private instance critical_ge_one:Fact (1≤(6/5:ℝ≥0∞)):=⟨one_le_sixFifths⟩

theorem exists_nativeCompactChart_critical_solution_bound
    (g:RiemannianMetric 3 M) (hY:0<Target.yamabeConstant g)
    (e:OpenPartialHomeomorph E M)
    (he:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei:ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {K:Set E} (hK:IsCompact K) (hKs:K⊆e.source) :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(b:M→ℝ) (hb:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ b)
      (hsmall:60*(∫x,|b x|^6 ∂g.volumeMeasure)^(2/3:ℝ)≤Target.yamabeConstant g)
      (f:E→ℝ),MemLp f (6/5:ℝ≥0∞) volume→
      ∃w:H1Zero g.leviCivitaData univ,
        ENNReal.ofReal ‖w‖≤C*eLpNorm f (6/5:ℝ≥0∞) volume ∧
        (∀η:H1Zero g.leviCivitaData univ,
          closedYamabeJacobianForm g b hb w η=
            ∫x,nativeCompactChartFunction e K f x*toL2 g.leviCivitaData univ η x ∂g.volumeMeasure) ∧
        (∀φ:EnergyTest g.leviCivitaData univ,
          (∫x,(-8*g.leviCivitaData.laplacian φ x+
            g.leviCivitaData.scalarCurvature x*φ x-30*b x^4*φ x)*
              toL2 g.leviCivitaData univ w x ∂g.volumeMeasure)=
            ∫x,φ x*nativeCompactChartFunction e K f x ∂g.volumeMeasure) := by
  obtain ⟨D,hD,hd⟩:=exists_nativeCompactChart_critical_bound g e he hei hK hKs
  obtain ⟨C,hC,hc⟩:=exists_uniform_closedSixFifthsJacobianSolution_bound g hY
  refine ⟨ENNReal.ofReal C*D,by finiteness,fun b hb hsmall f hf=>?_⟩
  have hF:=hd f hf
  let F:=hF.1.toLp (nativeCompactChartFunction e K f)
  let T:=closedSixFifthsJacobianSolutionCLM g hY b hb hsmall
  let w:=T F
  have he:ENNReal.ofReal ‖F‖=eLpNorm (nativeCompactChartFunction e K f) (6/5:ℝ≥0∞) g.volumeMeasure:=by
    rw [ofReal_norm]
    exact Lp.enorm_toLp hF.1
  refine ⟨w,?_,?_,?_⟩
  · calc
      _ ≤ ENNReal.ofReal (C*‖F‖):=ENNReal.ofReal_le_ofReal
        ((T.le_opNorm F).trans (mul_le_mul_of_nonneg_right (hc b hb hsmall).1 (norm_nonneg F)))
      _ = ENNReal.ofReal C*ENNReal.ofReal ‖F‖:=ENNReal.ofReal_mul hC.le
      _ ≤ _:=by rw [he];exact (mul_le_mul le_rfl hF.2 zero_le zero_le).trans_eq (by ring)
  · intro η
    change closedYamabeJacobianForm g b hb
      (closedYamabeJacobianInverse g hY b hb hsmall (closedSixFifthsForcing g hY F)) η=_
    rw [closedYamabeJacobianInverse_spec,closedSixFifthsForcing_apply]
    apply integral_congr_ae
    filter_upwards [hF.1.coeFn_toLp] with x hx
    change F x*_= _
    rw [show F x=nativeCompactChartFunction e K f x from hx]
  · intro φ
    have hh:=closedSixFifthsJacobianSolution_native_test g hY b hb hsmall F φ
    refine hh.trans (integral_congr_ae ?_)
    filter_upwards [hF.1.coeFn_toLp] with x hx
    change φ x*F x= _
    rw [show F x=nativeCompactChartFunction e K f x from hx]

#print axioms exists_nativeCompactChart_critical_solution_bound
end Yamabe3.Analysis.SpherePolar
