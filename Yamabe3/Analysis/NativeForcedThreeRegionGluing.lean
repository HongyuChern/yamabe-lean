import Yamabe3.Analysis.NativeForcedSourceUniqueness
import Yamabe3.Analysis.NativeForcedEnergyLocality

/-! SAME completed field, same piecewise source. Actual local H2-source
production at the interface is separate from the two side equations;
source uniqueness glues it across the volume-null sphere. No flux
cancellation or global equation is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Set Filter MeasureTheory PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
attribute [local instance] Classical.propDecidable
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem nativeForcedEnergySpace_mono_domain
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    {U V:Set M} (hVU:V⊆U) (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (h:(W,F)∈nativeForcedEnergySpace g B hB U):
    (W,F)∈nativeForcedEnergySpace g B hB V:=fun φ hs=>h φ (hs.trans hVU)

theorem nativeForcedEnergySpace_three_regions
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (Inside Closed Collar:Set M) (hInside:IsOpen Inside) (hClosed:IsClosed Closed)
    (hCol:IsOpen Collar) (hIC:Inside⊆Closed)
    (hBoundary:Closed\Inside⊆Collar) (hNull:g.volumeMeasure (Closed\Inside)=0)
    (W:H1Zero g.leviCivitaData univ) (Fi Fo:Lp ℝ 2 g.volumeMeasure)
    (hi:(W,Fi)∈nativeForcedEnergySpace g B hB Inside)
    (ho:(W,Fo)∈nativeForcedEnergySpace g B hB Closedᶜ)
    (hLocal:∀x∈Collar,∃U:Set M,IsOpen U ∧ x∈U ∧ U⊆Collar ∧
      ∃G:Lp ℝ 2 g.volumeMeasure,(W,G)∈nativeForcedEnergySpace g B hB U):
    ∃F:Lp ℝ 2 g.volumeMeasure,
      (F:M→ℝ)=ᵐ[g.volumeMeasure]Inside.piecewise (Fi:M→ℝ) (Fo:M→ℝ) ∧
      (W,F)∈nativeForcedEnergySpace g B hB univ:=by
  have hm:MemLp (Inside.piecewise (Fi:M→ℝ) (Fo:M→ℝ)) 2 g.volumeMeasure:=
    MemLp.piecewise hInside.measurableSet ((Lp.memLp Fi).restrict Inside) ((Lp.memLp Fo).restrict Insideᶜ)
  let F:=hm.toLp (Inside.piecewise (Fi:M→ℝ) (Fo:M→ℝ))
  have hF:(F:M→ℝ)=ᵐ[g.volumeMeasure]Inside.piecewise (Fi:M→ℝ) (Fo:M→ℝ):=hm.coeFn_toLp
  have hFi:(F:M→ℝ)=ᵐ[g.volumeMeasure.restrict Inside](Fi:M→ℝ):=by
    filter_upwards [ae_restrict_of_ae (s:=Inside) hF,ae_restrict_mem hInside.measurableSet] with x hx hxI
    exact hx.trans (piecewise_eq_of_mem _ _ _ hxI)
  have hFo:(F:M→ℝ)=ᵐ[g.volumeMeasure.restrict Closedᶜ](Fo:M→ℝ):=by
    filter_upwards [ae_restrict_of_ae (s:=Closedᶜ) hF,ae_restrict_mem hClosed.measurableSet.compl] with x hx hxO
    exact hx.trans (piecewise_eq_of_notMem _ _ _ (fun hxI=>hxO (hIC hxI)))
  have hiF:=nativeForcedEnergy_congr_source g B hB hInside.measurableSet W Fi F hFi.symm hi
  have hoF:=nativeForcedEnergy_congr_source g B hB hClosed.measurableSet.compl W Fo F hFo.symm ho
  refine ⟨F,hF,nativeForcedEnergySpace_of_local g B hB univ W F ?_⟩
  intro x _
  by_cases hxI:x∈Inside
  · exact ⟨Inside,hInside,hxI,hiF⟩
  by_cases hxO:x∈Closedᶜ
  · exact ⟨Closedᶜ,hClosed.isOpen_compl,hxO,hoF⟩
  have hxC:x∈Closed:=by simpa using hxO
  obtain ⟨U,hU,hxU,hUCol,G,hG⟩:=hLocal x (hBoundary ⟨hxC,hxI⟩)
  have hGi:(G:M→ℝ)=ᵐ[g.volumeMeasure.restrict (U∩Inside)](Fi:M→ℝ):=
    nativeForcedEnergy_source_unique g B hB (hU.inter hInside) W G Fi
      (nativeForcedEnergySpace_mono_domain g B hB inter_subset_left W G hG)
      (nativeForcedEnergySpace_mono_domain g B hB inter_subset_right W Fi hi)
  have hGo:(G:M→ℝ)=ᵐ[g.volumeMeasure.restrict (U∩Closedᶜ)](Fo:M→ℝ):=
    nativeForcedEnergy_source_unique g B hB (hU.inter hClosed.isOpen_compl) W G Fo
      (nativeForcedEnergySpace_mono_domain g B hB inter_subset_left W G hG)
      (nativeForcedEnergySpace_mono_domain g B hB inter_subset_right W Fo ho)
  have hGF:(G:M→ℝ)=ᵐ[g.volumeMeasure.restrict U](F:M→ℝ):=by
    have hnot:∀ᵐx:M∂g.volumeMeasure,x∉Closed\Inside:=by
      exact measure_eq_zero_iff_ae_notMem.mp hNull
    filter_upwards [ae_restrict_of_ae (s:=U) ((ae_restrict_iff' (hU.inter hInside).measurableSet).mp hGi),
      ae_restrict_of_ae (s:=U) ((ae_restrict_iff' (hU.inter hClosed.isOpen_compl).measurableSet).mp hGo),
      ae_restrict_of_ae (s:=U) hF,ae_restrict_of_ae (s:=U) hnot,ae_restrict_mem hU.measurableSet] with y hyi hyo hyF hyn hyU
    rw [hyF]
    by_cases hyI:y∈Inside
    · rw [piecewise_eq_of_mem _ _ _ hyI]
      exact hyi ⟨hyU,hyI⟩
    · have hyO:y∈Closedᶜ:=fun hyC=>hyn ⟨hyC,hyI⟩
      rw [piecewise_eq_of_notMem _ _ _ hyI]
      exact hyo ⟨hyU,hyO⟩
  exact ⟨U,hU,hxU,nativeForcedEnergy_congr_source g B hB hU.measurableSet W G F hGF hG⟩

theorem nativeForcedEnergySpace_global_all_tests
    (g:RiemannianMetric 3 M) (B:M→ℝ) (hB:ContMDiff (𝓡 3) 𝓘(ℝ,ℝ) ∞ B)
    (W:H1Zero g.leviCivitaData univ) (F:Lp ℝ 2 g.volumeMeasure)
    (h:(W,F)∈nativeForcedEnergySpace g B hB univ):
    ∀η:H1Zero g.leviCivitaData univ,closedYamabeJacobianForm g B hB W η=
      inner ℝ F (toL2 g.leviCivitaData univ η):=by
  intro η
  induction η using Completion.induction_on with
  | hp=>exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih φ=>exact h φ (subset_univ _)

#print axioms nativeForcedEnergySpace_mono_domain
#print axioms nativeForcedEnergySpace_three_regions
#print axioms nativeForcedEnergySpace_global_all_tests
end Yamabe3.Analysis.SpherePolar
