import Yamabe3.Analysis.NativeFullZeroCollar

/-! One actual compact physical H4 collar of the full-source solution.
The boundary lift is restored before gluing. The extension acts linearly
on the two representatives and respects their volume-a.e. identities. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory PoincareMT
open scoped NNReal ENNReal Topology ContDiff BoundedContinuousFunction Manifold
namespace Yamabe3.Analysis.UniformElliptic
open Delaunay SpherePolar SphereSpectrum PoincareMT.LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Euclidean
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "O" => Metric.ball (0:E) 1 \ {(0:E)}
local notation "X" => (E→ℝ) × (E→ℝ)

def fullModelCompletionPair {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1)
    (p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph) : X :=
  (toL2 nativeWeakEuclideanD O (fullModelZeroCompletion hκ0 hκ1 p f),fullModelEntranceLift p f)

theorem fullModelCompletionPair_rep {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1)
    (p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph) :
    (fun x=>(fullModelCompletionPair hκ0 hκ1 p f).1 x+(fullModelCompletionPair hκ0 hκ1 p f).2 x)
      =ᵐ[volume.restrict O] fullModelPhysicalField hκ0 hκ1 p f := by
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.sdiff isClosed_singleton).measurableSet,
    ae_restrict_of_ae (fullModelZeroCompletion_rep hκ0 hκ1 p f)] with x hx hr
  change toL2 nativeWeakEuclideanD O (fullModelZeroCompletion hκ0 hκ1 p f) x+fullModelEntranceLift p f x=_
  rw [hr,indicator_of_mem hx]
  exact fullModelPhysicalField_retained_entrance hκ0 hκ1 p f x

theorem exists_uniform_full_physical_local_collar_operator
    {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) (a:E) (ha:‖a‖=1) :
    ∃ (N:Set E) (L:X→ₗ[ℝ](E→ℝ)) (C:ℝ≥0∞),
      a∈N ∧ IsOpen N ∧ IsCompact (closure N) ∧ closure N⊆halfEndSourceAnnulus ∧ C≠⊤ ∧
      (∀u v:X,u.1 =ᵐ[volume] v.1 → u.2 =ᵐ[volume] v.2 → L u =ᵐ[volume.restrict N] L v) ∧
      ∀(p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph),
        let q:=fullModelCompletionPair hκ0 hκ1 p f
        MemWkp 4 2 (L q) N ∧ iteratedWeakSobolevNorm 4 2 (L q) N≤C*ENNReal.ofReal ‖f‖ ∧
        EqOn (L q) (fun x=>q.1 x+q.2 x) (N∩O) := by
  obtain ⟨N,T,A,haN,hN,hNc,hNs,hA,hAE,ht⟩:=exists_uniform_full_zero_physical_local_collar_ae_operator hκ0 hκ1 a ha
  obtain ⟨B,R,hB,hR,hb⟩:=exists_uniform_low_entrance_sobolev_bounds 4
  let L:X→ₗ[ℝ](E→ℝ):=T.comp (LinearMap.fst ℝ (E→ℝ) (E→ℝ))+LinearMap.snd ℝ (E→ℝ) (E→ℝ)
  refine ⟨N,L,A+B*ENNReal.ofReal ‖nativeSphereL2Inclusion‖,haN,hN,hNc,hNs,by finiteness,?_,?_⟩
  · intro u v hu hv
    filter_upwards [hAE u.1 v.1 hu,ae_restrict_of_ae hv] with x hx hy
    change T u.1 x+u.2 x=T v.1 x+v.2 x
    rw [hx,hy]
  intro p f
  have hz:=ht p f
  have hl:=hb (fun t=>p.orbit (t+p.phase))
    (p.smooth.continuous.comp (continuous_id.add continuous_const))
    (fun t=>p.bounded (t+p.phase)) (halfEndFullSourceAngularCLM f)
  have hNS:N⊆halfEndSourceAnnulus:=subset_closure.trans hNs
  have hBm:MemWkp 4 2 (fullModelEntranceLift p f) N:=hl.1.mono_set (by norm_num) hN hNS
  have hBn:iteratedWeakSobolevNorm 4 2 (fullModelEntranceLift p f) N≤
      (B*ENNReal.ofReal ‖nativeSphereL2Inclusion‖)*ENNReal.ofReal ‖f‖:=by
    have hn:=ENNReal.ofReal_le_ofReal (halfEndFullSourceAngular_norm_le f)
    rw [ENNReal.ofReal_mul (norm_nonneg nativeSphereL2Inclusion)] at hn
    exact (wkpNorm_mono_set (by norm_num) hN hNS hl.1).trans
      (hl.2.1.trans (by simpa only [mul_assoc] using mul_le_mul (a:=B) le_rfl hn zero_le zero_le))
  refine ⟨MemWkp.add (by norm_num) hN hz.1 hBm,?_,?_⟩
  · exact (wkpNorm_add_le (by norm_num) hN hz.1 hBm).trans
      ((add_le_add hz.2.1 hBn).trans_eq (by ring))
  · intro x hx
    change T (fullModelCompletionPair hκ0 hκ1 p f).1 x+_= _+_
    exact congrArg (fun t:ℝ=>t+fullModelEntranceLift p f x) (hz.2.2 hx)

theorem exists_uniform_full_compact_H4_collar_operator
    {κ:ℝ} (hκ0:0≤κ) (hκ1:κ<1) :
    ∃ (U:Set E) (L:X→ₗ[ℝ](E→ℝ)) (C:ℝ≥0∞),
      IsOpen U ∧ Metric.sphere (0:E) 1⊆U ∧ C≠⊤ ∧
      (∀u v:X,u.1 =ᵐ[volume] v.1 → u.2 =ᵐ[volume] v.2 → L u =ᵐ[volume] L v) ∧
      ∀(p:DelaunayPhaseData κ) (f:HalfEndPhysicalH2SourceGraph),
        let q:=fullModelCompletionPair hκ0 hκ1 p f
        HasCompactSupport (L q) ∧ MemWkp 4 2 (L q) univ ∧
        iteratedWeakSobolevNorm 4 2 (L q) univ≤C*ENNReal.ofReal ‖f‖ ∧
        EqOn (L q) (fun x=>q.1 x+q.2 x) (U∩O) := by
  classical
  let K:Set E:=Metric.sphere 0 1
  have hK:IsCompact K:=isCompact_sphere 0 1
  have hnorm (a:K):‖(a:E)‖=1:=by simpa only [K,Metric.mem_sphere,dist_zero_right] using a.2
  choose N L C haN hN hNc hNs hC hae hl using fun a:K=>
    exists_uniform_full_physical_local_collar_operator hκ0 hκ1 a (hnorm a)
  obtain ⟨s,U,ρ,hU,hKU,hρ,hρc,hρs,hpart⟩:=exists_finite_neighborhood_partition hK N hN haN
  obtain ⟨D,hD,hb⟩:=exists_finitePhysicalPatch_bound 4 (fun i:s=>N i.1)
    (fun i=>hN i.1) ρ hρ hρc hρs
  let T:X→ₗ[ℝ](E→ℝ):=
    {toFun:=fun u=>finitePhysicalPatch ρ (fun i:s=>L i.1 u)
     map_add':=by
       intro u v
       funext x
       simp only [finitePhysicalPatch,map_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]
     map_smul':=by
       intro c u
       funext x
       simp only [finitePhysicalPatch,map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
       simp only [mul_left_comm,Finset.mul_sum]}
  refine ⟨U,T,∑i:s,D i*C i.1,hU,hKU,
    ENNReal.sum_ne_top.mpr (fun i _=>ENNReal.mul_ne_top (hD i) (hC i.1)),?_,?_⟩
  · intro u v hu hv
    have hi (i:s):∀ᵐx∂volume,x∈N i.1→L i.1 u x=L i.1 v x:=
      (ae_restrict_iff' (hN i.1).measurableSet).mp (hae i.1 u v hu hv)
    filter_upwards [eventually_all.mpr hi] with x hx
    change (∑i:s,ρ i x*L i.1 u x)=∑i:s,ρ i x*L i.1 v x
    apply Finset.sum_congr rfl
    intro i _
    by_cases hn:x∈N i.1
    · rw [hx i hn]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht=>hn (hρs i ht)),zero_mul,zero_mul]
  intro p f
  let q:=fullModelCompletionPair hκ0 hκ1 p f
  have hh:=hb (fun i:s=>L i.1 q) (fun i=>(hl i.1 p f).1)
  refine ⟨finitePhysicalPatch_compact ρ _ hρc,hh.1,hh.2.trans ?_,?_⟩
  · calc
      _ ≤ ∑i:s,D i*(C i.1*ENNReal.ofReal ‖f‖):=
        Finset.sum_le_sum (fun i _=>mul_le_mul le_rfl (hl i.1 p f).2.1 zero_le zero_le)
      _ = _:=by simp only [Finset.sum_mul,mul_assoc]
  · exact finitePhysicalPatch_eq_on ρ (fun i:s=>L i.1 q) (fun x=>q.1 x+q.2 x) hρs hpart
      (fun i=>(hl i.1 p f).2.2)

#print axioms fullModelCompletionPair_rep
#print axioms exists_uniform_full_physical_local_collar_operator
#print axioms exists_uniform_full_compact_H4_collar_operator
end Yamabe3.Analysis.UniformElliptic
