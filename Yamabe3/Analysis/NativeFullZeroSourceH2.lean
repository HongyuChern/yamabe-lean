import Yamabe3.Analysis.NativeFullZeroCompletion
import Yamabe3.Analysis.NativeLowEntranceSobolev
import Yamabe3.Analysis.NativeHalfEndSourceChart
import Yamabe3.Analysis.DelaunayAnnularPotentialJets
import Yamabe3.Analysis.WeakLocalMultiplierExplicit

/-! The explicit entrance-corrected physical source is genuinely H2 on
an annulus crossing the sphere. Its homogeneous bound is uniform before
the actual orbit, phase and full source. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum
open Poincare.Analysis.Sobolev.Euclidean

theorem fullModelPotential_eq_neg_annular {κ:ℝ} (p:DelaunayPhaseData κ) :
    nativeHalfEndPotentialCoefficient p.potential=fun x=> -annularDelaunayPotential p.orbit p.phase x := by
  funext x
  change (15/4)*p.orbit (-Real.log ‖x‖+p.phase)^4/‖x‖^2=
    -(-(15/4)*p.orbit (p.phase-Real.log ‖x‖)^4/‖x‖^2)
  rw [show -Real.log ‖x‖+p.phase=p.phase-Real.log ‖x‖ by ring]
  ring

theorem exists_uniform_full_zero_source_entrance_H2_bound :
    ∃C:ℝ≥0∞,C≠⊤ ∧ ∀(κ:ℝ) (p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph),
      MemWkp 2 2 (fullModelZeroPhysicalSource p f) halfEndSourceAnnulus ∧
      iteratedWeakSobolevNorm 2 2 (fullModelZeroPhysicalSource p f) halfEndSourceAnnulus≤C*ENNReal.ofReal ‖f‖ := by
  obtain ⟨M,hM,hMj⟩:=exists_uniform_delaunay_annular_potential_jets 2
  obtain ⟨B,R,hB,hR,hb⟩:=exists_uniform_low_entrance_sobolev_bounds 2
  let J:ℝ≥0∞:=49*ENNReal.ofReal M
  let N:ℝ≥0∞:=ENNReal.ofReal ‖nativeSphereL2Inclusion‖
  refine ⟨8+8*(J*B+R)*N,by dsimp only [J,N];finiteness,?_⟩
  intro κ p f
  let F:=halfEndFullSourceAngularCLM f
  let v:ℝ→ℝ:=fun t=>p.orbit (t+p.phase)
  have hv:Continuous v:=p.smooth.continuous.comp (continuous_id.add continuous_const)
  have hvb:∀t,0≤v t ∧ v t≤1:=fun t=>p.bounded (t+p.phase)
  have hl:=hb v hv hvb F
  let L:=fullModelEntranceLift p f
  let H:=fullModelEntranceRHS p f
  let Q:=nativeHalfEndPotentialCoefficient p.potential
  have hQ:ContDiffOn ℝ ∞ Q ({(0:E)}ᶜ):=
    nativeHalfEndPotentialCoefficient_contDiffOn p.potential p.potential_smooth
  have hsub:closure halfEndSourceAnnulus⊆({(0:E)}ᶜ):=by
    intro x hx
    have hh:=NativeJacobianAnnulus.closure_sourceAnnulus_subset_outer hx
    change x≠0
    exact norm_pos_iff.mp (by linarith [hh.1])
  have hj:∀j≤2,∀x∈halfEndSourceAnnulus,‖iteratedFDeriv ℝ j Q x‖≤M:=by
    intro j hj x hx
    change ‖iteratedFDeriv ℝ j (nativeHalfEndPotentialCoefficient p.potential) x‖≤M
    rw [fullModelPotential_eq_neg_annular]
    change ‖iteratedFDeriv ℝ j (-annularDelaunayPotential p.orbit p.phase) x‖≤M
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact hMj p.orbit p.smooth (fun t=>⟨(p.bounded t).1,(p.bounded t).2,p.derivative_bound t⟩)
      p.ode p.phase j hj x (by linarith [hx.1]) (by linarith [hx.2])
  have hmul:=weak_local_multiplier_explicit_bound 2 halfEndSourceAnnulus_isOpen
    NativeJacobianAnnulus.sourceAnnulus_precompact isClosed_singleton.isOpen_compl hsub hQ hl.1 hM hj
  norm_num only [Nat.cast_ofNat,show (1+2*(3:ℝ≥0∞))^2=49 by norm_num] at hmul
  have hQN:iteratedWeakSobolevNorm 2 2 (fun x=>Q x*L x) halfEndSourceAnnulus≤J*B*ENNReal.ofReal ‖F‖:=
    hmul.2.trans (by
      simpa only [J,mul_assoc] using (mul_le_mul (a:=J) le_rfl hl.2.1 zero_le zero_le))
  have hneg:MemWkp 2 2 (fun x=>(-1:ℝ)*H x) halfEndSourceAnnulus:=
    MemWkp.const_smul (by norm_num) halfEndSourceAnnulus_isOpen hl.2.2.1 (-1)
  have hnegN:iteratedWeakSobolevNorm 2 2 (fun x=>(-1:ℝ)*H x) halfEndSourceAnnulus≤R*ENNReal.ofReal ‖F‖:=by
    have hm:MemWkp 2 2 H halfEndSourceAnnulus:=hl.2.2.1
    rw [wkpNorm_const_smul (by norm_num) halfEndSourceAnnulus_isOpen hm]
    simp only [enorm_neg,enorm_one,one_mul]
    exact hl.2.2.2
  let T:E→ℝ:=fun x=>Q x*L x+(-1)*H x
  have hT:MemWkp 2 2 T halfEndSourceAnnulus:=MemWkp.add (by norm_num) halfEndSourceAnnulus_isOpen hmul.1 hneg
  have hTN:iteratedWeakSobolevNorm 2 2 T halfEndSourceAnnulus≤(J*B+R)*ENNReal.ofReal ‖F‖:=
    (wkpNorm_add_le (by norm_num) halfEndSourceAnnulus_isOpen hmul.1 hneg).trans
      ((add_le_add hQN hnegN).trans_eq (by ring))
  have hs:=halfEndH2SourceGraph_entrance_H2_bound f
  have h8T:=MemWkp.const_smul (by norm_num) halfEndSourceAnnulus_isOpen hT 8
  have hsum:=MemWkp.add (by norm_num) halfEndSourceAnnulus_isOpen hs.1 h8T
  have heq:(fun x=>halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f) x+8*T x)=
      fullModelZeroPhysicalSource p f:=by
    funext x
    change _+8*(Q x*L x+(-1)*H x)=_+8*(Q x*L x-H x)
    ring
  refine ⟨heq ▸ hsum,?_⟩
  rw [←heq]
  have h8TN:iteratedWeakSobolevNorm 2 2 (fun x=>(8:ℝ)*T x) halfEndSourceAnnulus≤
      8*((J*B+R)*ENNReal.ofReal ‖F‖):=by
    rw [wkpNorm_const_smul (by norm_num) halfEndSourceAnnulus_isOpen hT]
    simpa only [Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤8),ENNReal.ofReal_ofNat] using
      mul_le_mul (a:=(8:ℝ≥0∞)) le_rfl hTN zero_le zero_le
  have hFN:ENNReal.ofReal ‖F‖≤N*ENNReal.ofReal ‖f‖:=by
    simpa only [N,ENNReal.ofReal_mul (norm_nonneg nativeSphereL2Inclusion)] using
      ENNReal.ofReal_le_ofReal (halfEndFullSourceAngular_norm_le f)
  calc
    _ ≤ iteratedWeakSobolevNorm 2 2 (halfEndEuclideanPhysicalSource (halfEndPhysicalH2SourceGraphValue f)) halfEndSourceAnnulus+
        iteratedWeakSobolevNorm 2 2 (fun x=>(8:ℝ)*T x) halfEndSourceAnnulus:=
      wkpNorm_add_le (by norm_num) halfEndSourceAnnulus_isOpen hs.1 h8T
    _ ≤ 8*ENNReal.ofReal ‖f‖+8*((J*B+R)*ENNReal.ofReal ‖F‖):=add_le_add hs.2 h8TN
    _ ≤ 8*ENNReal.ofReal ‖f‖+8*((J*B+R)*(N*ENNReal.ofReal ‖f‖)):=
      add_le_add le_rfl (mul_le_mul le_rfl (mul_le_mul le_rfl hFN zero_le zero_le) zero_le zero_le)
    _ = _:=by ring

#print axioms fullModelPotential_eq_neg_annular
#print axioms exists_uniform_full_zero_source_entrance_H2_bound
end Yamabe3.Analysis.UniformElliptic
