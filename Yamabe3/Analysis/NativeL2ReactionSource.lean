import Yamabe3.Analysis.NativeForcedEnergySpace

/-! A computed L2 compensation and the SAME field's L2 reaction
construct ONE native source class before every test. The full source
representative and its pairings are preserved exactly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Filter MeasureTheory PoincareMT
open scoped ContDiff Manifold Topology ENNReal lp RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

 theorem exists_nativeL2_same_field_reaction_source
    (g:RiemannianMetric 3 M) (q:M→ℝ) (Z:H1Zero g.leviCivitaData univ)
    (hq:MemLp (fun y=>q y*toL2 g.leviCivitaData univ Z y) 2 g.volumeMeasure)
    (C:Lp ℝ 2 g.volumeMeasure):
    ∃F:Lp ℝ 2 g.volumeMeasure,
      (F:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>C y+8*q y*toL2 g.leviCivitaData univ Z y) ∧
      ∀η:EnergyTest g.leviCivitaData univ,
        inner ℝ F (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ))=
          inner ℝ C (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ))+
          (∫y,8*q y*toL2 g.leviCivitaData univ Z y*η y ∂g.volumeMeasure):=by
  let Q:=hq.toLp (fun y=>q y*toL2 g.leviCivitaData univ Z y)
  let F:=C+(8:ℝ) • Q
  have hQa:(Q:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>q y*toL2 g.leviCivitaData univ Z y):=hq.coeFn_toLp
  have hF:(F:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>C y+8*q y*toL2 g.leviCivitaData univ Z y):=by
    filter_upwards [Lp.coeFn_add C ((8:ℝ) • Q),Lp.coeFn_smul (8:ℝ) Q,hQa] with y hy hs hq
    change F y=_ at hy
    rw [hy]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hq]
    ring
  refine ⟨F,hF,fun η=>?_⟩
  change inner ℝ (C+(8:ℝ) • Q) _=_
  rw [inner_add_left]
  apply congrArg (fun r:ℝ=>inner ℝ C (toL2 g.leviCivitaData univ (η:H1Zero g.leviCivitaData univ))+r)
  rw [L2.inner_def,toL2_coe]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (8:ℝ) Q,hQa,η.memLp.coeFn_toLp] with y hs hq hη
  simp only [Real.inner_apply]
  change ((8:ℝ) • Q:Lp ℝ 2 g.volumeMeasure) y*(η.memLp.toLp η) y=_
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hq,hη]
  ring

#print axioms exists_nativeL2_same_field_reaction_source
end Yamabe3.Analysis.SpherePolar
