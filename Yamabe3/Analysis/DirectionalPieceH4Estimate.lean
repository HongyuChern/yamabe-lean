import Yamabe3.Analysis.DirectionalPieceH3Estimate
import Yamabe3.Analysis.DirectionalSecondSourceBound
import Yamabe3.Analysis.DirectionalPieceSourceBound
import Yamabe3.Analysis.DirectionalPieceH4
import Yamabe3.Analysis.BoundaryFourthDerivativeRecovery

/-! Quantitative H4 recovery on one side from two actual tangential source
derivatives. The common bound N is a bound on the listed actual input norms,
not an elliptic estimate assumption. The half-space wrapper supplies it. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic Poincare.Analysis.Elliptic.Iteration
local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem sum_tangential_le {a : Fin 3 → ℝ≥0∞} {N : ℝ≥0∞}
    (h : ∀ k : Fin 3,k≠0 → a k≤N) :
    (∑ k ∈ (Finset.univ : Finset (Fin 3)).erase 0,a k)≤3*N := by
  classical
  calc
    _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin 3)).erase 0,N :=
      Finset.sum_le_sum (fun k hk => h k (Finset.mem_erase.mp hk).1)
    _ ≤ ∑ _k : Fin 3,N :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => zero_le)
    _ = _ := by simp [nsmul_eq_mul]

theorem exists_directional_piece_H4_bound
    (B : SmoothEllipticBilinearForm 3 univ)
    {O V W : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V⊆O)
    (hW : IsOpen W) (hWV : W⊆V) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ (N : ℝ≥0∞) (u f : E → ℝ)
      (r : Fin 3 → E → ℝ) (t : Fin 3 → Fin 3 → E → ℝ),
      MemWkp 2 2 u O → MemLp f 2 (volume.restrict O) → MemWkp 2 2 f W →
      (∀ k : Fin 3,k≠0 → MemLp (r k) 2 (volume.restrict O)) →
      (∀ k : Fin 3,k≠0 → HasWeakPartialDeriv k (r k) f O) →
      (∀ k s : Fin 3,k≠0 → s≠0 → MemLp (t k s) 2 (volume.restrict O)) →
      (∀ k s : Fin 3,k≠0 → s≠0 → HasWeakPartialDeriv s (t k s) (r k) O) →
      iteratedWeakSobolevNorm 2 2 u O≤N → iteratedWeakSobolevNorm 2 2 f W≤N →
      (∀ k : Fin 3,k≠0 → iteratedWeakSobolevNorm 0 2 (r k) O≤N) →
      (∀ k s : Fin 3,k≠0 → s≠0 → iteratedWeakSobolevNorm 0 2 (t k s) O≤N) →
      (∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆O →
        (∫ x in O,∑ i,∑ j,B.a x i j*chosenWeakPartial' 2 j u O x*
          fderiv ℝ φ x (EuclideanSpace.single i 1))=∫ x in O,f x*φ x) →
      MemWkp 4 2 u W ∧ iteratedWeakSobolevNorm 4 2 u W≤C*N := by
  classical
  have hWc : IsCompact (closure W) := hVc.of_isClosed_subset isClosed_closure (closure_mono hWV)
  have hWO : W⊆O := hWV.trans (subset_closure.trans hVO)
  obtain ⟨U,hU,hVU,hUO⟩ := hVc.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hVO)
  have hUc : IsCompact (closure U) := hOc.of_isClosed_subset isClosed_closure (hUO.trans subset_closure)
  have hsub : U⊆O := subset_closure.trans hUO
  have hWU : W⊆U := hWV.trans (subset_closure.trans hVU)
  obtain ⟨K,hK,hKu⟩ := exists_directional_piece_H3_estimate B hO hOc hV hVc hVO hW hWV
  obtain ⟨P,hP,hPp⟩ := exists_directional_piece_H3_estimate B hU hUc hV hVc hVU hW hWV
  choose D hD hbD using fun k : Fin 3 => exists_directional_H2_estimate B hO hOc hU hUc hUO k
  choose L hL hbL using fun k : Fin 3 => exists_explicit_directional_piece_H1_bound hW hWc B.a B.smooth_a k
  choose A hA hbA using fun k s : Fin 3 => exists_second_directional_source_bound hU hUc B.a B.smooth_a k s
  obtain ⟨Kn,hKn,hn⟩ := exists_normal_H4_recovery_bound B hW hWc
  let D0 : ℝ≥0∞ := 2*∑ k : Fin 3,D k
  let L0 : ℝ≥0∞ := ∑ k : Fin 3,L k
  let A0 : ℝ≥0∞ := ∑ k : Fin 3,∑ s : Fin 3,A k s
  let K3 : ℝ≥0∞ := 5*K
  let H : ℝ≥0∞ := P*(D0+(1+L0*K3)+3*(1+A0*(1+D0)))
  have hDS : (∑ k : Fin 3,D k)≠⊤ := ENNReal.sum_ne_top.mpr (fun k _ => hD k)
  have hD0 : D0≠⊤ := by dsimp [D0]; finiteness
  have hL0 : L0≠⊤ := ENNReal.sum_ne_top.mpr (fun k _ => hL k)
  have hA0 : A0≠⊤ := ENNReal.sum_ne_top.mpr (fun k _ => ENNReal.sum_ne_top.mpr (fun s _ => hA k s))
  have hK3 : K3≠⊤ := by dsimp [K3]; finiteness
  have hH : H≠⊤ := by dsimp [H]; finiteness
  refine ⟨Kn*(K3+1+3*H),by finiteness,?_⟩
  intro N u f r t hu hf hfW hr hfr ht hrt huN hfN hrN htN heq
  have hu3 := hKu u f r hu hf hfW.le_succ hr hfr heq
  have hu3N : iteratedWeakSobolevNorm 3 2 u W≤K3*N := by
    calc
      _ ≤ K*(iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 1 2 f W+
          ∑ k ∈ (Finset.univ : Finset (Fin 3)).erase 0,iteratedWeakSobolevNorm 0 2 (r k) O) := hu3.2
      _ ≤ K*(N+N+3*N) := mul_le_mul le_rfl
        (add_le_add (add_le_add huN ((wkpNorm_mono_order (by norm_num : 1≤2) f W).trans hfN))
          (sum_tangential_le hrN)) zero_le zero_le
      _ = _ := by dsimp [K3]; ring
  have huU := hu.mono_set (by norm_num : (1:ℝ≥0∞)≤2) hU hsub
  have huUN : iteratedWeakSobolevNorm 2 2 u U≤N := (wkpNorm_mono_set (by norm_num) hU hsub hu).trans huN
  have hfU := hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have heqU := localized_principal_restrict_canonical hU hsub hu.memW1p heq
  have hpU (k : Fin 3) (hk : k≠0) : MemWkp 2 2 (chosenWeakPartial' 2 k u U) U ∧
      iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k u U) U≤D0*N := by
    have hh := hbD k u f (r k) hu hf (hr k hk) (hfr k hk) heq
    have he := chosenWeakPartial'_mono_set_ae (by norm_num : (1:ℝ≥0∞)≤2) hU hsub hu.memW1p k
    refine ⟨(MemWkp_congr_ae (by norm_num) hU he).mp hh.1,?_⟩
    rw [← wkpNorm_congr_ae (k:=2) (by norm_num : (1:ℝ≥0∞)≤2) hU he]
    calc
      _ ≤ D k*(iteratedWeakSobolevNorm 2 2 u O+iteratedWeakSobolevNorm 0 2 (r k) O) := hh.2
      _ ≤ (∑ j : Fin 3,D j)*(N+N) := mul_le_mul
        (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ k)) (add_le_add huN (hrN k hk)) zero_le zero_le
      _ = _ := by dsimp [D0]; ring
  have hpWN (k : Fin 3) (hk : k≠0) :
      iteratedWeakSobolevNorm 3 2 (chosenWeakPartial' 2 k u W) W≤H*N := by
    let G := differentiatedSource B.a (fun j => chosenWeakPartial' 2 j u U)
      (fun i j => chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u U) U) (r k) k
    have hrU := (hr k hk).mono_measure (Measure.restrict_mono hsub le_rfl)
    have hfrU := (hfr k hk).restrict hU hsub
    have hGe := explicit_directional_source_equation hU hUc B.a B.smooth_a huU hfU hrU k hfrU heqU
    have hGW : MemWkp 1 2 G W :=
      explicit_directional_source_H1_on_piece hW hWc hWU B.a B.smooth_a huU hu3.1 hfW hrU k hfrU
    have hGN : iteratedWeakSobolevNorm 1 2 G W≤(1+L0*K3)*N := by
      calc
        _ ≤ iteratedWeakSobolevNorm 2 2 f W+L k*iteratedWeakSobolevNorm 3 2 u W :=
          hbL k hWU u f (r k) huU hu3.1 hfW hrU hfrU
        _ ≤ N+L0*(K3*N) := add_le_add hfN (mul_le_mul
          (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ k)) hu3N zero_le zero_le)
        _ = _ := by ring
    have hT (s : Fin 3) (hs : s≠0) : ∃ T : E → ℝ, MemLp T 2 (volume.restrict U) ∧
        HasWeakPartialDeriv s T G U ∧ iteratedWeakSobolevNorm 0 2 T U≤(1+A0*(1+D0))*N := by
      have htU := (ht k s hk hs).mono_measure (Measure.restrict_mono hsub le_rfl)
      have hrtU := (hrt k s hk hs).restrict hU hsub
      obtain ⟨T,hTm,hTw,hTn⟩ := hbA k s u (r k) (t k s) huU (hpU s hs).1 hrU htU hrtU
      refine ⟨T,hTm,hTw,hTn.trans ?_⟩
      have htUN : iteratedWeakSobolevNorm 0 2 (t k s) U≤N :=
        (wkpNorm_mono_set (k:=0) (by norm_num) hU hsub (ht k s hk hs)).trans (htN k s hk hs)
      have ha0 : A k s≤A0 := (Finset.single_le_sum (f:=fun s => A k s)
        (fun _ _ => zero_le) (Finset.mem_univ s)).trans
        (Finset.single_le_sum (f:=fun k : Fin 3 => ∑ s : Fin 3,A k s)
          (fun _ _ => zero_le) (Finset.mem_univ k))
      calc
        _ ≤ N+A0*(N+D0*N) := add_le_add htUN
          (mul_le_mul ha0 (add_le_add huUN (hpU s hs).2) zero_le zero_le)
        _ = _ := by ring
    let T : Fin 3 → E → ℝ := fun s => if hs : s=0 then 0 else Classical.choose (hT s hs)
    have hTs (s : Fin 3) (hs : s≠0) : MemLp (T s) 2 (volume.restrict U) ∧
        HasWeakPartialDeriv s (T s) G U ∧ iteratedWeakSobolevNorm 0 2 (T s) U≤(1+A0*(1+D0))*N := by
      simpa only [T,dif_neg hs] using Classical.choose_spec (hT s hs)
    have hh := hPp (chosenWeakPartial' 2 k u U) G T (hpU k hk).1 hGe.1 hGW
      (fun s hs => (hTs s hs).1) (fun s hs => (hTs s hs).2.1) hGe.2
    rw [← wkpNorm_congr_ae (k:=3) (by norm_num : (1:ℝ≥0∞)≤2) hW
      (chosenWeakPartial'_mono_set_ae (by norm_num) hW hWU huU.memW1p k)]
    calc
      _ ≤ P*(iteratedWeakSobolevNorm 2 2 (chosenWeakPartial' 2 k u U) U+
          iteratedWeakSobolevNorm 1 2 G W+
          ∑ s ∈ (Finset.univ : Finset (Fin 3)).erase 0,iteratedWeakSobolevNorm 0 2 (T s) U) := hh.2
      _ ≤ P*(D0*N+(1+L0*K3)*N+3*((1+A0*(1+D0))*N)) :=
        mul_le_mul le_rfl (add_le_add (add_le_add (hpU k hk).2 hGN)
          (sum_tangential_le (fun s hs => (hTs s hs).2.2))) zero_le zero_le
      _ = _ := by dsimp [H]; ring
  have hu4 := directional_source_H4_on_piece B hO hOc hV hVc hVO hW hWV hu hf hfW r hr hfr
    (fun k s hk hs => ⟨hr k hk,t k s,ht k s hk hs,hrt k s hk hs⟩) heq
  refine ⟨hu4,?_⟩
  calc
    _ ≤ Kn*(iteratedWeakSobolevNorm 3 2 u W+iteratedWeakSobolevNorm 2 2 f W+
        ∑ k ∈ (Finset.univ : Finset (Fin 3)).erase 0,iteratedWeakSobolevNorm 3 2 (chosenWeakPartial' 2 k u W) W) :=
      hn u f hu4 hfW (localized_principal_restrict_canonical hW hWO hu.memW1p heq)
    _ ≤ Kn*(K3*N+N+3*(H*N)) := mul_le_mul le_rfl
      (add_le_add (add_le_add hu3N hfN) (sum_tangential_le hpWN)) zero_le zero_le
    _ = _ := by ring

#print axioms exists_directional_piece_H4_bound
end Yamabe3.Analysis.UniformElliptic
