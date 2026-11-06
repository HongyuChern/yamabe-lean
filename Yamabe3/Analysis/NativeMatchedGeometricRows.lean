import Yamabe3.Analysis.NativeMatchedDelaunayCollar

/-! The actual native geometric error is applied to the full same-source
jet. Its decay is uniform before the Delaunay orbit and every scale. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay
variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1) (B : NativeHighPotential) (p : DelaunayPhaseData κ)
  (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ)

def nativeMatchedGeometricRowCLM (g : RiemannianMetric 3 E) (ε s : ℝ) :
    Lp AngularSpectralSpace 2 (volume : Measure ℝ) →L[ℝ] NativeCollarL2 :=
  (nativeFullCollarJetErrorCLM g (ε*Real.exp (-s)) p.orbit p.smooth (p.phase+s)).comp
    (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s)

omit B p hp in
theorem exists_uniform_nativeMatchedGeometricRow_decay
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀ a ∈ Λ, (g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀ a ∈ Λ, (g a).pullbackVolumeDensity id 0=1) :
    ∃ C : ℝ,0<C ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀ t,(∫ s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀ ε : ℝ,0 ≤ ε → ε ≤ 1 → ∀ a ∈ Λ, ∀ s : ℝ,0 ≤ s →
        ‖nativeMatchedGeometricRowCLM hκ0 hκ1 B p hp (g a) ε s‖≤C*ε*Real.exp (-s) := by
  obtain ⟨C,hC,hc⟩ := exists_native_full_collar_error_linear_bound Λ g hB hρ
  obtain ⟨L,hL0,hb⟩ := exists_uniform_nativeMatchedDelaunayJet_bound hκ0 hκ1
  refine ⟨C*L,by positivity,fun B p hp ε hε hε1 a ha s hs => ?_⟩
  have he : Real.exp (-s)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  have h := hc (ε*Real.exp (-s)) (by positivity)
    ((mul_le_of_le_one_right hε he).trans hε1) a ha p.orbit p.smooth
    (fun t => ⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩) p.ode (p.phase+s)
    (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F)
  have hn := (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s).le_of_opNorm_le (hb B p hp s) F
  exact (h.trans (mul_le_mul_of_nonneg_left hn (by positivity))).trans_eq (by ring)

#print axioms exists_uniform_nativeMatchedGeometricRow_decay
end Yamabe3.Analysis.SpherePolar
