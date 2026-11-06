import Yamabe3.Analysis.NativeH4ResidualCancellation
import Yamabe3.Analysis.NativeTwoSidedGlobalPhysicalEquation

/-! The cancelled shell pairings identify one actual L2 residual as zero
on the punctured ball. Shell Jacobians and volume costs are retained.
This step uses only the residual's L2 bound, not a false L2 assumption on
the original cylinder source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open SpherePolar SphereSpectrum Delaunay
attribute [local irreducible] nativeFullShellSourceReturnCLM nativeTwoSidedJacobianRowCLM
variable (P : NativeHighPotential)
  (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|P.potential (t-s)|)≤P.κ)
  (v₀ : ℝ→ℝ) (hv : Continuous v₀) (hb : ∀t,0≤v₀ t ∧ v₀ t≤1)
  (b : ℝ) {τ : ℝ} (ht : 0<τ)

def nativeH4ResidualPhysicalRow (g : RiemannianMetric 3 E) (ε : ℝ)
    (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource) (n : ℕ) : NativeCollarL2 :=
  nativeH4MatchedGeometricRowCLM (fullBubbleHighPotential (-τ)) P hp g ε
    (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n) x+
    nativeTwoSidedJacobianRowCLM P hp v₀ hv hb τ g ε (nativeLogShellCenter n) Y

theorem exists_nativeH4ResidualPhysicalRow_bound
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃C : ℝ,0<C ∧ ∀ε : ℝ,0≤ε → ε≤1 → ∀a∈Λ,
      ∀(x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource) (n : ℕ),
        ‖nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) (g a) ε x Y n‖≤C*(‖x‖+‖Y‖) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeH4MatchedGeometricRow_decay (fullBubbleHighPotential (-τ)) P hp Λ g hB hρ
  obtain ⟨D,hD,hd⟩ := exists_nativeTwoSidedJacobianRow_bound P hp v₀ hv hb τ Λ g hB hρ
  refine ⟨C+D,by positivity,fun ε hε hε1 a ha x Y n => ?_⟩
  have h1 := (nativeH4MatchedGeometricRowCLM (fullBubbleHighPotential (-τ)) P hp (g a) ε
    (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n)).le_of_opNorm_le
      (hc ε hε hε1 a ha (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n)) x
  have hexp : Real.exp (-nativeLogShellCenter n)≤1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (nativeLogShellCenter_nonneg n))
  have hm : C*ε*Real.exp (-nativeLogShellCenter n)≤C :=
    (mul_le_of_le_one_right (mul_nonneg hC.le hε) hexp).trans (mul_le_of_le_one_right hC.le hε1)
  have h1' := h1.trans (mul_le_mul_of_nonneg_right hm (norm_nonneg x))
  have h2 := hd ε hε hε1 a ha (nativeLogShellCenter n) (nativeLogShellCenter_nonneg n) Y
  apply (norm_add_le _ _).trans
  apply (add_le_add h1' h2).trans
  nlinarith [mul_nonneg hC.le (norm_nonneg Y),mul_nonneg hD.le (norm_nonneg x)]

theorem nativeH4Residual_physical_zero
    (hpot : P.potential=delaunayPhasePotentialBCF v₀ hv hb 0)
    {ι : Type*} (Λ : Finset ι) (g : ι→RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (a : ι) (ha : a∈Λ)
    (x : HalfEndPhysicalH4Graph) (Y : NativeTwoSidedSource)
    (hY : Y=nativeH4MatchedGlobalResidualCLM P hp ht (g a) ε x+
      nativeSupportedTwoSidedGlobalSourceCLM P hp v₀ hv hb b ht (g a) ε Y) :
    let R := nativePhysicalShellAssembly (nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) (g a) ε x Y)
    MemLp R 2 (volume.restrict (Metric.ball 0 1 \ {(0:E)})) ∧
      R=ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})] (fun _ => 0) := by
  obtain ⟨C,hC,hc⟩ := exists_nativeH4ResidualPhysicalRow_bound P hp v₀ hv hb (τ:=τ) Λ g hB hρ
  let U := nativeH4ResidualPhysicalRow P hp v₀ hv hb (τ:=τ) (g a) ε x Y
  have hU := hc ε hε hε1 a ha x Y
  have hCxy : 0≤C*(‖x‖+‖Y‖) := by positivity
  have hm := nativePhysicalShellAssembly_memLp U hCxy hU
  refine ⟨hm,?_⟩
  have hz : nativePhysicalShellAssembly U=ᵐ[volume.restrict (Metric.ball 0 1 \ {(0:E)})]
      (fun _ => -(0:ℝ)) := by
    apply nativePhysicalTest_ae_eq_negative hm MemLp.zero'
    intro φ hφ hcs hs
    have h0 : (0:E)∉tsupport φ := fun h => (hs h).2 (by simp)
    let G := nativePhysicalPairTestL2 φ hφ hcs h0
    have hsum := nativeH4MatchedResidual_cancellation P hp v₀ hv hb b ht hpot Λ g hB hρ ε hε hε1 a ha x Y hY
      G (nativePhysicalPairTestL2_positive φ hφ hcs h0 hs)
    have ht' : HasSum (fun n => Real.exp (-5*nativeLogShellCenter n/2)*
        (∫y in nativeSourceShell,(U n : E→ℝ) y*φ (Real.exp (-nativeLogShellCenter n) • y))) 0 := by
      simpa only [U,nativeH4ResidualPhysicalRow,G,nativeFullShellSourceReturn_physical_test] using hsum
    have he := (nativePhysicalShellAssembly_test_hasSum U hCxy hU φ hφ.continuous hcs).unique ht'
    simpa only [zero_mul,integral_zero,neg_zero] using he
  simpa only [neg_zero] using hz

#print axioms exists_nativeH4ResidualPhysicalRow_bound
#print axioms nativeH4Residual_physical_zero
end Yamabe3.Analysis.UniformElliptic
