import Yamabe3.Analysis.NativePhysicalShellRow

/-! A bounded family of actual collar rows gives one physical L2
representative on the punctured ball. Disjoint shells and their volume
cost justify the assembly and every subsequent integral sum. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory PoincareMT
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace Yamabe3.Analysis.SpherePolar

 def nativePhysicalShellAssembly (U : ℕ → NativeCollarL2) (x : E) : ℝ :=
  ∑'n,(nativePhysicalShell n).indicator (nativePhysicalShellRow n (U n)) x

 theorem nativePhysicalShellAssembly_on (U : ℕ → NativeCollarL2) (n : ℕ) {x : E}
    (hx : x∈nativePhysicalShell n) : nativePhysicalShellAssembly U x=nativePhysicalShellRow n (U n) x := by
  rw [nativePhysicalShellAssembly,tsum_eq_single n]
  · exact indicator_of_mem hx _
  · intro m hm
    exact indicator_of_notMem (fun hy => (disjoint_left.mp (nativePhysicalShell_disjoint hm)) hy hx) _

 theorem nativePhysicalShellAssembly_off (U : ℕ → NativeCollarL2) {x : E}
    (hx : x∉Metric.ball 0 1 \ {(0:E)}) : nativePhysicalShellAssembly U x=0 := by
  have hz (n : ℕ) : (nativePhysicalShell n).indicator (nativePhysicalShellRow n (U n)) x=0 :=
    indicator_of_notMem (fun hn => hx (by rw [←nativePhysicalShell_union];exact mem_iUnion.mpr ⟨n,hn⟩)) _
  simp only [nativePhysicalShellAssembly,hz,tsum_zero]

 theorem nativePhysicalShellAssembly_memLp (U : ℕ → NativeCollarL2) {C : ℝ}
    (hC : 0≤C) (hU : ∀n,‖U n‖≤C) :
    MemLp (nativePhysicalShellAssembly U) 2 (volume.restrict (Metric.ball 0 1 \ {(0:E)})) := by
  have he (n : ℕ) : nativePhysicalShellAssembly U=ᵐ[volume.restrict (nativePhysicalShell n)] nativePhysicalShellRow n (U n) :=
    (ae_restrict_iff' (nativePhysicalShell_measurable n)).mpr
      (Eventually.of_forall (fun x hx => nativePhysicalShellAssembly_on U n hx))
  have hm (n : ℕ) : MemLp (nativePhysicalShellAssembly U) 2 (volume.restrict (nativePhysicalShell n)) :=
    (nativePhysicalShellRow_memLp n (U n)).ae_eq (he n).symm
  have hmeas : AEStronglyMeasurable (nativePhysicalShellAssembly U)
      (volume.restrict (Metric.ball 0 1 \ {(0:E)})) := by
    rw [←nativePhysicalShell_union]
    exact AEStronglyMeasurable.iUnion (fun n => (hm n).1)
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  rw [←nativePhysicalShell_union]
  apply integrableOn_iUnion_of_summable_integral_norm (fun n => (hm n).integrable_sq)
  apply (nativeLogShell_decay_summable.mul_left (C^2)).of_norm_bounded
  intro n
  have heq : (∫x in nativePhysicalShell n,‖nativePhysicalShellAssembly U x^2‖)=
      ∫x in nativePhysicalShell n,nativePhysicalShellRow n (U n) x^2 := by
    apply integral_congr_ae
    filter_upwards [he n] with x hx
    rw [hx,Real.norm_of_nonneg (sq_nonneg _)]
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _)),heq]
  have hnorm : ‖U n‖^2≤C^2 := by nlinarith [norm_nonneg (U n),hU n]
  have hdecay : Real.exp (-2*nativeLogShellCenter n)≤Real.exp (-nativeLogShellCenter n) :=
    Real.exp_le_exp.mpr (by linarith [nativeLogShellCenter_nonneg n])
  calc
    _≤Real.exp (-2*nativeLogShellCenter n)*‖U n‖^2 := nativePhysicalShellRow_square_bound n (U n)
    _≤Real.exp (-nativeLogShellCenter n)*C^2 := mul_le_mul hdecay hnorm (sq_nonneg _) (Real.exp_pos _).le
    _=C^2*Real.exp (-nativeLogShellCenter n) := mul_comm _ _

 theorem nativePhysicalShellAssembly_test_hasSum (U : ℕ → NativeCollarL2) {C : ℝ}
    (hC : 0≤C) (hU : ∀n,‖U n‖≤C) (φ : E → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    HasSum (fun n => Real.exp (-5*nativeLogShellCenter n/2)*
      (∫x in nativeSourceShell,(U n : E → ℝ) x*φ (Real.exp (-nativeLogShellCenter n) • x)))
      (∫x in Metric.ball 0 1 \ {(0:E)},nativePhysicalShellAssembly U x*φ x) := by
  have hm := nativePhysicalShellAssembly_memLp U hC hU
  have hp : MemLp φ 2 (volume.restrict (Metric.ball 0 1 \ {(0:E)})) :=
    (hφ.memLp_of_hasCompactSupport hc).restrict _
  have hi := hm.integrable_mul hp
  have his : IntegrableOn (fun x => nativePhysicalShellAssembly U x*φ x) (⋃n,nativePhysicalShell n) := by
    rw [nativePhysicalShell_union]
    exact hi
  have hs := hasSum_integral_iUnion nativePhysicalShell_measurable nativePhysicalShell_disjoint his
  rw [nativePhysicalShell_union] at hs
  have he (n : ℕ) : (∫x in nativePhysicalShell n,nativePhysicalShellAssembly U x*φ x)=
      Real.exp (-5*nativeLogShellCenter n/2)*
        (∫x in nativeSourceShell,(U n : E → ℝ) x*φ (Real.exp (-nativeLogShellCenter n) • x)) := by
    rw [←nativePhysicalShellRow_test_integral]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (nativePhysicalShell_measurable n)] with x hx
    rw [nativePhysicalShellAssembly_on U n hx]
  simpa only [he] using hs

#print axioms nativePhysicalShellAssembly_on
#print axioms nativePhysicalShellAssembly_off
#print axioms nativePhysicalShellAssembly_memLp
#print axioms nativePhysicalShellAssembly_test_hasSum
end Yamabe3.Analysis.SpherePolar
