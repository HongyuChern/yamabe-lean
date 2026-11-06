import Yamabe3.Analysis.NativePointWeakRemoval
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Local native weak-test identities glue on the actual compact test
support. A finite smooth partition is constructed; no global PDE or
boundary cancellation is inferred from unproved structure fields. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open Set Filter MeasureTheory Metric PoincareMT UniformSpace
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar
open PoincareMT.LeviCivitaData.Dirichlet
variable {M:Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
private def nativeLocalGluingH1Normed (g:RiemannianMetric 3 M) :
    NormedSpace ℝ (H1Zero g.leviCivitaData univ):=inferInstance
attribute [local instance] nativeLocalGluingH1Normed

theorem native_local_tests_determine_on_support
    (g:RiemannianMetric 3 M) (L:H1Zero g.leviCivitaData univ →L[ℝ] ℝ) (Ω:Set M)
    (hlocal:∀x∈Ω,∃V:Set M,IsOpen V ∧ x∈V ∧
      ∀ψ:EnergyTest g.leviCivitaData univ,tsupport (ψ:M→ℝ)⊆V →L (ψ:H1Zero g.leviCivitaData univ)=0)
    (φ:EnergyTest g.leviCivitaData univ) (hs:tsupport (φ:M→ℝ)⊆Ω) :
    L (φ:H1Zero g.leviCivitaData univ)=0 := by
  classical
  choose N hN hxN hz using fun x:tsupport (φ:M→ℝ)=>hlocal x (hs x.property)
  choose b hb0 hb using fun x:tsupport (φ:M→ℝ)=>
    (SmoothBumpFunction.nhds_basis_tsupport (I:=𝓡 3) (x:M)).mem_iff.mp ((hN x).mem_nhds (hxN x))
  let W(x:tsupport (φ:M→ℝ)):Set M:={y|(b x:M→ℝ)=ᶠ[𝓝 y]1}
  have hW(x:tsupport (φ:M→ℝ)):IsOpen (W x):=isOpen_setOf_eventually_nhds
  have hcover:tsupport (φ:M→ℝ)⊆⋃x,W x:=by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,(b ⟨x,hx⟩).eventuallyEq_one⟩
  obtain ⟨s,hsub⟩:=φ.hasCompactSupport.isCompact.elim_finite_subcover W hW hcover
  let U:Set M:=⋃i:s,W i.1
  let B:BumpCovering s M U:={
    toFun:=fun i=>⟨b i.1,(b i.1).continuous⟩
    locallyFinite':=locallyFinite_of_finite _
    nonneg':=fun i x=>((b i.1).mem_Icc).1
    le_one':=fun i x=>((b i.1).mem_Icc).2
    eventuallyEq_one':=fun x hx=>by
      obtain ⟨i,hi⟩:=mem_iUnion.mp hx
      exact ⟨i,hi⟩ }
  let ρ:=B.toSmoothPartitionOfUnity (fun i=>(b i.1).contMDiff)
  let ψ:s→EnergyTest g.leviCivitaData univ:=fun i=>φ.mulSmooth (ρ i) (ρ i).contMDiff
  have hψs(i:s):tsupport (ψ i:M→ℝ)⊆N i.1:=
    (φ.mulSmooth_support_subset (ρ i) (ρ i).contMDiff).trans
      ((closure_mono (B.support_toPartitionOfUnity_subset i)).trans (hb i.1))
  have hsum:φ=∑i:s,ψ i:=by
    apply Subtype.ext
    funext x
    rw [EnergyTest.coe_sum]
    simp only [Finset.sum_apply,ψ,EnergyTest.mulSmooth_apply]
    by_cases hx:x∈tsupport (φ:M→ℝ)
    · have hxU:x∈U:=by
        obtain ⟨i,hi,hix⟩:=mem_iUnion₂.mp (hsub hx)
        exact mem_iUnion.mpr ⟨⟨i,hi⟩,hix⟩
      have hp:=ρ.sum_eq_one hxU
      have hp':(∑i:s,ρ i x)=1:=by simpa only [finsum_eq_sum_of_fintype] using hp
      rw [←Finset.sum_mul,hp',one_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero,Finset.sum_const_zero]
  have hsumH:(φ:H1Zero g.leviCivitaData univ)=∑i:s,(ψ i:H1Zero g.leviCivitaData univ):=by
    let I:EnergyTest g.leviCivitaData univ →L[ℝ] H1Zero g.leviCivitaData univ:=Completion.toComplL
    change I φ=∑i:s,I (ψ i)
    rw [←map_sum]
    exact congrArg I hsum
  calc
    _ = L (∑i:s,(ψ i:H1Zero g.leviCivitaData univ)):=congrArg L hsumH
    _ = ∑i:s,L (ψ i:H1Zero g.leviCivitaData univ):=map_sum L _ _
    _ = 0:=Finset.sum_eq_zero (fun i _=>hz i.1 (ψ i) (hψs i))

#print axioms native_local_tests_determine_on_support
end Yamabe3.Analysis.SpherePolar
