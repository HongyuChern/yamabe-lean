import Yamabe3.Analysis.NativeSmoothPotentialResponseEquation

/-! Exact same-field feedback cancellation. Two actual native equations
and one equality in H1 give the smooth target operator with the computed
compensation sum. The omitted potential is cancelled, not renamed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory Metric PoincareMT
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open UniformElliptic PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

 theorem nativeSmoothPotential_same_fixed_field_equation
    (g:RiemannianMetric 3 M) (Ω:Set M) (qFull qs:M→ℝ)
    (hSm:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ qs)
    (z₀ dz u:H1Zero g.leviCivitaData univ) (hu:u=z₀+dz)
    (C₀ C₁ F₀ F₁:Lp ℝ 2 g.volumeMeasure)
    (hF₀:(F₀:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>C₀ y+8*qFull y*toL2 g.leviCivitaData univ z₀ y))
    (hF₁:(F₁:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>C₁ y+8*qFull y*toL2 g.leviCivitaData univ dz y-
      8*((qFull y-qs y)*toL2 g.leviCivitaData univ u y)))
    (hforced₀:(z₀,F₀)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const Ω)
    (hforced₁:(dz,F₁)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const Ω):
    let V:M→ℝ:=fun y=>g.leviCivitaData.scalarCurvature y-8*qs y
    let hV:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V:=g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul hSm)
    ∃Ft:Lp ℝ 2 g.volumeMeasure,
      (Ft:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>(C₀+C₁:Lp ℝ 2 g.volumeMeasure) y+8*qs y*toL2 g.leviCivitaData univ u y) ∧
      (u,Ft)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const Ω ∧
      (u,C₀+C₁)∈NativeWeakEllipticDataSpace g Ω V hV:=by
  dsimp only
  let Ft:Lp ℝ 2 g.volumeMeasure:=F₀+F₁
  let Ct:Lp ℝ 2 g.volumeMeasure:=C₀+C₁
  let V:M→ℝ:=fun y=>g.leviCivitaData.scalarCurvature y-8*qs y
  have hV:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ V:=g.leviCivitaData.contMDiff_scalarCurvature.sub (contMDiff_const.mul hSm)
  have huval:(toL2 g.leviCivitaData univ u:M→ℝ)=ᵐ[g.volumeMeasure]
      (fun y=>toL2 g.leviCivitaData univ z₀ y+toL2 g.leviCivitaData univ dz y):=by
    rw [hu,map_add]
    exact Lp.coeFn_add _ _
  have hFt:(Ft:M→ℝ)=ᵐ[g.volumeMeasure](fun y=>Ct y+8*qs y*toL2 g.leviCivitaData univ u y):=by
    filter_upwards [Lp.coeFn_add F₀ F₁,Lp.coeFn_add C₀ C₁,hF₀,hF₁,huval] with y hft hct hf₀ hf₁ huv
    change (F₀+F₁:Lp ℝ 2 g.volumeMeasure) y=_
    rw [hft]
    change F₀ y+F₁ y=_
    rw [hf₀,hf₁]
    change _=(C₀+C₁:Lp ℝ 2 g.volumeMeasure) y+_
    rw [hct]
    simp only [Pi.add_apply]
    linear_combination -8*qFull y*huv
  have hforced:(u,Ft)∈nativeForcedEnergySpace g (fun _:M=>0) contMDiff_const Ω:=by
    intro η hη
    rw [hu]
    have hl:=congrArg (fun L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ=>L (η:H1Zero g.leviCivitaData univ))
      (map_add (closedYamabeJacobianForm g (fun _:M=>0) contMDiff_const) z₀ dz)
    have h₀:=hforced₀ η hη
    have h₁:=hforced₁ η hη
    change _=inner ℝ (F₀+F₁) _
    rw [inner_add_left]
    exact hl.trans (congrArg₂ (·+·) h₀ h₁)
  have hDataR:=nativeForcedEnergySpace_mem_data g (fun _:M=>0) contMDiff_const Ω u Ft hforced
  refine ⟨Ft,hFt,hforced,?_⟩
  intro ζ
  let η:H1Zero g.leviCivitaData univ:=nativeDomainEnergyInclusion g Ω ζ
  have hd:=hDataR ζ
  rw [nativeWeakEnergySourceDataCLM_apply,nativeRestrictedEllipticForm_apply,
    nativeRestrictedPotentialForm_integral,nativeRestrictedL2SourceOperator_apply] at hd ⊢
  simp only [nativeJacobianPotential,zero_pow (by decide:(4:ℕ)≠0),mul_zero,sub_zero] at hd
  have hiV:=nativeRestrictedPotentialForm_integrable g Ω V hV u η
  have hiR:=nativeRestrictedPotentialForm_integrable g Ω g.leviCivitaData.scalarCurvature g.leviCivitaData.contMDiff_scalarCurvature u η
  have hiC:=nativeRestrictedL2SourceOperator_integrable g Ω Ct η
  have hiF:=nativeRestrictedL2SourceOperator_integrable g Ω Ft η
  have hInt:(∫y in Ω,V y*toL2 g.leviCivitaData univ u y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)-
      (∫y in Ω,Ct y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)=
      (∫y in Ω,g.leviCivitaData.scalarCurvature y*toL2 g.leviCivitaData univ u y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure)-
      (∫y in Ω,Ft y*toL2 g.leviCivitaData univ η y ∂g.volumeMeasure):=by
    rw [←integral_sub hiV hiC,←integral_sub hiR hiF]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (s:=Ω) hFt] with y hy
    dsimp only [V,Pi.sub_apply]
    rw [hy]
    ring
  linear_combination hd+hInt

#print axioms nativeSmoothPotential_same_fixed_field_equation
end Yamabe3.Analysis.SpherePolar
