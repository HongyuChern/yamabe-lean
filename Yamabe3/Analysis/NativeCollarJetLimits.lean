import Yamabe3.Analysis.NativeCollarJetTrace

/-! Strong limits and actual boundary restriction limits use the same
C2 approximants. The closure is proved from volume jets; boundary values
are never inferred by restricting an arbitrary volume-a.e. equality. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory PoincareMT
open Yamabe3.Analysis.UniformElliptic
open scoped Topology ContDiff
namespace Yamabe3.Analysis.SpherePolar

variable {ι : Type*}

theorem nativeC2CollarJet_series_tendsto (u : ι → nativeC2OffZero)
    (hv : Summable (fun i => nativeC2CollarValue (u i).property))
    (hp : ∀ j,Summable (fun i => nativeC2CollarFirst (u i).property j))
    (hs : ∀ k j,Summable (fun i => nativeC2CollarSecond (u i).property k j)) :
    Tendsto (fun s : Finset ι => nativeC2CollarJetLinear (∑ i ∈ s,u i)) atTop
      (𝓝 ((∑' i,nativeC2CollarValue (u i).property),
        (fun j => ∑' i,nativeC2CollarFirst (u i).property j),
        (fun k j => ∑' i,nativeC2CollarSecond (u i).property k j))) := by
  have h := hv.hasSum.prodMk_nhds
    ((tendsto_pi_nhds.mpr (fun j => (hp j).hasSum)).prodMk_nhds
      (tendsto_pi_nhds.mpr (fun k => tendsto_pi_nhds.mpr (fun j => (hs k j).hasSum))))
  change Tendsto _ atTop _ at h
  apply h.congr'
  apply Eventually.of_forall
  intro s
  symm
  dsimp only
  rw [map_sum]
  apply Prod.ext
  · simp [nativeC2CollarJetLinear,nativeC2ValueLinear,Function.prod,Prod.fst_sum]
  · apply Prod.ext
    · funext j
      simp [nativeC2CollarJetLinear,Function.prod,Prod.fst_sum,Prod.snd_sum,LinearMap.pi_apply,Finset.sum_apply,
        nativeC2FirstLinear,nativeL2WeakDerivativeLinearMap]
    · funext k j
      simp [nativeC2CollarJetLinear,Function.prod,Prod.fst_sum,Prod.snd_sum,LinearMap.pi_apply,Finset.sum_apply,
        nativeC2SecondLinear,nativeL2WeakDerivativeLinearMap]

theorem nativeCollarJet_series_mem (u : ι → nativeC2OffZero)
    (hv : Summable (fun i => nativeC2CollarValue (u i).property))
    (hp : ∀ j,Summable (fun i => nativeC2CollarFirst (u i).property j))
    (hs : ∀ k j,Summable (fun i => nativeC2CollarSecond (u i).property k j)) :
    ((∑' i,nativeC2CollarValue (u i).property),
      (fun j => ∑' i,nativeC2CollarFirst (u i).property j),
      (fun k j => ∑' i,nativeC2CollarSecond (u i).property k j)) ∈ nativeCollarJetClosure :=
  nativeCollarJetClosure_of_tendsto (nativeC2CollarJet_series_tendsto u hv hp hs)

theorem nativeCollarValueTrace_of_C2_limit {l : Filter ι} [NeBot l]
    (u : ι → nativeC2OffZero) (J : nativeCollarJetClosure)
    (hJ : Tendsto (fun a => nativeC2CollarJetLinear (u a)) l (𝓝 J.val))
    {τ : Lp ℝ 2 angularVolume} (hτ : Tendsto (fun a => nativeC2ValueTraceLinear (u a)) l (𝓝 τ)) :
    nativeCollarValueTraceCLM J=τ := by
  have hi : Tendsto (fun a => nativeC2CollarJetInclusion (u a)) l (𝓝 J) := tendsto_subtype_rng.mpr hJ
  have ht := nativeCollarValueTraceCLM.continuous.continuousAt.tendsto.comp hi
  have ht' := ht.congr' (Eventually.of_forall fun a => (nativeCollarTraceCLM_agrees_C2 (u a)).1)
  exact tendsto_nhds_unique ht' hτ

theorem nativeCollarNormalTrace_of_C2_limit {l : Filter ι} [NeBot l]
    (u : ι → nativeC2OffZero) (J : nativeCollarJetClosure)
    (hJ : Tendsto (fun a => nativeC2CollarJetLinear (u a)) l (𝓝 J.val))
    {ν : Lp ℝ 2 angularVolume} (hν : Tendsto (fun a => nativeC2NormalTraceLinear (u a)) l (𝓝 ν)) :
    nativeCollarNormalTraceCLM J=ν := by
  have hi : Tendsto (fun a => nativeC2CollarJetInclusion (u a)) l (𝓝 J) := tendsto_subtype_rng.mpr hJ
  have ht := nativeCollarNormalTraceCLM.continuous.continuousAt.tendsto.comp hi
  have ht' := ht.congr' (Eventually.of_forall fun a => (nativeCollarTraceCLM_agrees_C2 (u a)).2)
  exact tendsto_nhds_unique ht' hν

#print axioms nativeC2CollarJet_series_tendsto
#print axioms nativeCollarJet_series_mem
#print axioms nativeCollarValueTrace_of_C2_limit
#print axioms nativeCollarNormalTrace_of_C2_limit
end Yamabe3.Analysis.SpherePolar
