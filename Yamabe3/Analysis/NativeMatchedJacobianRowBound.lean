import Yamabe3.Analysis.NativeMatchedGeometricRows
import Yamabe3.Analysis.NativeOrbitCollarJacobian
import Yamabe3.Analysis.NativePhysicalShellAssembly

/-! Uniform full native operator rows, including the matched boundary
field, have the square-integrability budget required by physical assembly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff lp RealInnerProductSpace BoundedContinuousFunction
namespace Yamabe3.Analysis.SpherePolar
open SphereSpectrum Yamabe3.Analysis.Delaunay

theorem nativeFlatCollarJet_norm_bound (V : ℝ →ᵇ ℝ) (J : NativeCollarJet) :
    ‖nativeFlatCollarJetCLM V J‖≤(3+‖V‖*Real.exp 1)*‖J‖ := by
  have hp : ‖nativeCollarPotentialMulCLM V J.1‖≤(‖V‖*Real.exp 1)*‖J.1‖ :=
    l2ScalarMul_norm_le (nativeHalfEndPotentialCoefficient V)
      (nativeCollarPotential_measurable V).aestronglyMeasurable (‖V‖*Real.exp 1)
      (by positivity) (by
        filter_upwards [ae_restrict_mem (nativePolarTimeWindow_open (1/2)).measurableSet] with x hx
        exact nativeCollarPotential_bound V hx) J.1
  have hj (i j : Fin 3) : ‖J.2.2 i j‖≤‖J‖ :=
    (norm_le_pi_norm (J.2.2 i) j).trans ((norm_le_pi_norm J.2.2 i).trans
      ((norm_snd_le J.2).trans (norm_snd_le J)))
  have hsum : ‖∑j : Fin 3,J.2.2 j j‖≤3*‖J‖ :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hj j j)).trans_eq (by simp))
  change ‖-((∑j : Fin 3,J.2.2 j j)+nativeCollarPotentialMulCLM V J.1)‖≤_
  rw [norm_neg]
  apply (norm_add_le _ _).trans
  apply (add_le_add hsum (hp.trans (mul_le_mul_of_nonneg_left (norm_fst_le J) (by positivity)))).trans_eq
  ring

variable {κ : ℝ} (hκ0 : 0≤κ) (hκ1 : κ<1)

theorem exists_uniform_nativeMatchedJacobianRow_bound
    {ι : Type*} (Λ : Finset ι) (g : ι → RiemannianMetric 3 E)
    (hB : ∀a∈Λ,(g a).euclideanCoefficients 0=innerSL ℝ)
    (hρ : ∀a∈Λ,(g a).pullbackVolumeDensity id 0=1) :
    ∃C : ℝ,0<C ∧ ∀ (B : NativeHighPotential) (p : DelaunayPhaseData κ)
      (hp : ∀t,(∫s : ℝ,spectralMajorant (5/2) 2 s*|p.potential (t-s)|)≤κ),
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ a ∈ Λ, ∀ s : ℝ, 0 ≤ s → ∀ F,
      ‖nativeOrbitCollarJacobianCLM (g a) (ε*Real.exp (-s)) p.orbit p.smooth p.bounded (p.phase+s)
        (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F)‖≤C*‖F‖ := by
  obtain ⟨L,hL,hj⟩ := exists_uniform_nativeMatchedDelaunayJet_bound hκ0 hκ1
  obtain ⟨D,hD,hd⟩ := exists_uniform_nativeMatchedGeometricRow_decay hκ0 hκ1 Λ g hB hρ
  let C := (3+(15/4:ℝ)*Real.exp 1)*L+D
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,fun B p hp ε hε hε1 a ha s hs F => ?_⟩
  let J := nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s F
  let V := delaunayPhasePotentialBCF p.orbit p.smooth.continuous p.bounded (p.phase+s)
  have hJ : ‖J‖≤L*‖F‖ := (nativeMatchedDelaunayRawJetCLM hκ0 hκ1 B p hp s).le_of_opNorm_le (hj B p hp s) F
  have hV : ‖V‖≤15/4 := delaunayPhasePotentialBCF_norm_le _ _ _ _
  have hflat := (nativeFlatCollarJet_norm_bound V J).trans
    (mul_le_mul (add_le_add_right (mul_le_mul_of_nonneg_right hV (Real.exp_pos 1).le) 3) hJ
      (norm_nonneg _) (by positivity))
  have herr := (nativeMatchedGeometricRowCLM hκ0 hκ1 B p hp (g a) ε s).le_of_opNorm_le
    (hd B p hp ε hε hε1 a ha s hs) F
  have he : Real.exp (-s)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
  have hsmall : D*ε*Real.exp (-s)≤D :=
    (mul_le_of_le_one_right (mul_nonneg hD.le hε) he).trans (mul_le_of_le_one_right hD.le hε1)
  have herr' : ‖nativeFullCollarJetErrorCLM (g a) (ε*Real.exp (-s)) p.orbit p.smooth (p.phase+s) J‖≤D*‖F‖ :=
    herr.trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg F))
  change ‖nativeFlatCollarJetCLM V J+nativeFullCollarJetErrorCLM (g a) (ε*Real.exp (-s)) p.orbit p.smooth (p.phase+s) J‖≤_
  exact (norm_add_le _ _).trans ((add_le_add hflat herr').trans_eq (by dsimp only [C];ring))

#print axioms nativeFlatCollarJet_norm_bound
#print axioms exists_uniform_nativeMatchedJacobianRow_bound
end Yamabe3.Analysis.SpherePolar
