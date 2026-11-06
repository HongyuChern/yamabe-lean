import Yamabe3.Analysis.UniformElliptic.H4CanonicalLimit
import Yamabe3.Analysis.UniformElliptic.WeakSobolevCauchyLimit
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sequences

/-!
# A complete graph space of actual weak Sobolev jets

The graph lies in an existing Banach space: a value space times a uniformly
bounded family of finite L1 sums of genuine L2 coordinate jets. Membership
means that each jet is the actual weak derivative of the declared value.
Closedness is proved using the closed weak-derivative graph and pointwise
convergence of the same values. Thus the first projection is injective;
there are no independent or freely assigned derivative fields.

The native weighted source and solution graphs are concrete instances in a
separate module. This reusable construction does not assume smooth density.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Sobolev.Euclidean
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- All coordinate tuples through order k; orders zero through four have
exactly 1+3+9+27+81 entries. -/
abbrev WeakSobolevJetIndex (k : ℕ) := Σ j : Fin (k + 1), Fin j.1 → Fin 3

/-- One genuine finite sum of L2 jet norms, rather than their maximum. -/
abbrev WeakSobolevJetBlock (V : Set E3) (k : ℕ) :=
  PiLp 1 (fun _ : WeakSobolevJetIndex k => Lp ℝ 2 (volume.restrict V))

/-- Uniformly bounded actual jet blocks over a specified index family. -/
abbrev WeakSobolevJetFamily (I : Type*) (V : Set E3) (k : ℕ) :=
  lp (fun _ : I => WeakSobolevJetBlock V k) ⊤

variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def weakSobolevJetEval (V : Set E3) (k : ℕ) (i : I) (β : WeakSobolevJetIndex k) :
    WeakSobolevJetFamily I V k →L[ℝ] Lp ℝ 2 (volume.restrict V) :=
  (PiLp.proj 1 (fun _ : WeakSobolevJetIndex k => Lp ℝ 2 (volume.restrict V)) β).comp
    (lp.evalCLM ℝ (fun _ : I => WeakSobolevJetBlock V k) ⊤ i)

@[simp] theorem weakSobolevJetEval_apply (V : Set E3) (k : ℕ) (i : I)
    (β : WeakSobolevJetIndex k) (z : WeakSobolevJetFamily I V k) :
    weakSobolevJetEval V k i β z = z i β := rfl

/-- The graph is defined by actual weak derivatives of the given physical
value map P. The bounded family stores those derivatives as genuine L2
classes on the explicitly retained chart domain V. -/
def weakSobolevGraph (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) :
    Submodule ℝ (X × WeakSobolevJetFamily I V k) where
  carrier := {z | ∀ i : I, MemWkp k 2 (P z.1 i) V ∧
    ∀ β : WeakSobolevJetIndex k,
      (z.2 i β : E3 → ℝ) =ᵐ[volume.restrict V]
        iterWeakPartial 2 β.1.1 β.2 (P z.1 i) V}
  zero_mem' := by
    intro i
    constructor
    · change MemWkp k 2 (P 0 i) V
      rw [map_zero]
      change MemWkp k 2 (fun _ : E3 => 0) V
      exact MemWkp_zero_fun (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV
    · intro β
      change ((0 : Lp ℝ 2 (volume.restrict V)) : E3 → ℝ) =ᵐ[volume.restrict V]
        iterWeakPartial 2 β.1.1 β.2 (P 0 i) V
      simp only [map_zero, Pi.zero_apply]
      have hzero : ((0 : Lp ℝ 2 (volume.restrict V)) : E3 → ℝ)
          =ᵐ[volume.restrict V] (fun _ : E3 => 0) := Lp.coeFn_zero ℝ 2 (volume.restrict V)
      exact hzero.trans
        (iterWeakPartial_ae_zero_of_input_ae_zero (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          hV β.1.1 β.2 (Eventually.of_forall fun _ => rfl)).symm
  add_mem' := by
    intro x y hx hy i
    have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    have hP : P (x.1 + y.1) i = fun z => P x.1 i z + P y.1 i z := by
      funext z
      simp only [map_add, Pi.add_apply]
    constructor
    · change MemWkp k 2 (P (x.1 + y.1) i) V
      rw [hP]
      exact MemWkp.add hp hV (hx i).1 (hy i).1
    · intro β
      change ((x.2 i β + y.2 i β : Lp ℝ 2 (volume.restrict V)) : E3 → ℝ)
        =ᵐ[volume.restrict V] iterWeakPartial 2 β.1.1 β.2 (P (x.1 + y.1) i) V
      rw [hP]
      have hj : β.1.1 ≤ k := Nat.le_of_lt_succ β.1.2
      have hderiv := iterWeakPartial_add_ae hp hV β.2
        ((hx i).1.le_of_le hj) ((hy i).1.le_of_le hj)
      filter_upwards [Lp.coeFn_add (x.2 i β) (y.2 i β), (hx i).2 β, (hy i).2 β,
        hderiv] with z hsum hxx hyy hdd
      simp only [Pi.add_apply, hxx, hyy] at hsum
      exact hsum.trans hdd.symm
  smul_mem' := by
    intro c x hx i
    have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    have hP : P (c • x.1) i = fun z => c * P x.1 i z := by
      funext z
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    constructor
    · change MemWkp k 2 (P (c • x.1) i) V
      rw [hP]
      exact MemWkp.const_smul hp hV (hx i).1 c
    · intro β
      change ((c • x.2 i β : Lp ℝ 2 (volume.restrict V)) : E3 → ℝ)
        =ᵐ[volume.restrict V] iterWeakPartial 2 β.1.1 β.2 (P (c • x.1) i) V
      rw [hP]
      have hj : β.1.1 ≤ k := Nat.le_of_lt_succ β.1.2
      have hderiv := iterWeakPartial_const_smul_ae hp hV β.2
        ((hx i).1.le_of_le hj) c
      filter_upwards [Lp.coeFn_smul c (x.2 i β), (hx i).2 β, hderiv] with z hsm hxz hdz
      simp only [Pi.smul_apply, smul_eq_mul, hxz] at hsm
      exact hsm.trans hdz.symm

/-- The declared value uniquely determines every L2 jet in the graph. -/
theorem weakSobolevGraph_fst_injective (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) :
    Function.Injective (fun z : weakSobolevGraph V hV k P => z.1.1) := by
  intro x y hxy
  change x.1.1 = y.1.1 at hxy
  apply Subtype.ext
  apply Prod.ext hxy
  ext i β
  have hx := (x.2 i).2 β
  have hy := (y.2 i).2 β
  rw [hxy] at hx
  exact hx.trans hy.symm

/-- Closedness is proved from actual weak derivatives and pointwise value
continuity. The jet limits are first genuine L2 limits and are then
identified by the closed derivative graph with the same physical value. -/
theorem weakSobolevGraph_isClosed (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ))
    (hP : ∀ i : I, ∀ x : E3, Continuous (fun f : X => P f i x)) :
    IsClosed (weakSobolevGraph V hV k P : Set (X × WeakSobolevJetFamily I V k)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro z Z hz hZ
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hvalue : Tendsto (fun n => (z n).1) atTop (𝓝 Z.1) :=
    continuous_fst.continuousAt.tendsto.comp hZ
  have hjets : Tendsto (fun n => (z n).2) atTop (𝓝 Z.2) :=
    continuous_snd.continuousAt.tendsto.comp hZ
  intro i
  let v : ∀ j : ℕ, (Fin j → Fin 3) → E3 → ℝ := fun j β =>
    if hj : j ≤ k then (Z.2 i ⟨⟨j, Nat.lt_succ_of_le hj⟩, β⟩ : E3 → ℝ) else 0
  have hv (j : ℕ) (β : Fin j → Fin 3) (hj : j ≤ k) :
      MemLp (v j β) 2 (volume.restrict V) := by
    simpa only [v, dif_pos hj] using
      Lp.memLp (Z.2 i ⟨⟨j, Nat.lt_succ_of_le hj⟩, β⟩)
  have ht (j : ℕ) (β : Fin j → Fin 3) (hj : j ≤ k) :
      Tendsto (fun n => eLpNorm
        (fun x => iterWeakPartial 2 j β (P (z n).1 i) V x - v j β x)
          2 (volume.restrict V)) atTop (𝓝 0) := by
    let β' : WeakSobolevJetIndex k := ⟨⟨j, Nat.lt_succ_of_le hj⟩, β⟩
    have hcoord : Tendsto (fun n => (z n).2 i β') atTop (𝓝 (Z.2 i β')) := by
      simpa only [Function.comp_def, weakSobolevJetEval_apply] using
        (weakSobolevJetEval V k i β').continuous.continuousAt.tendsto.comp hjets
    have hlp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (z n).2 i β')
      (Z.2 i β')).mp hcoord
    apply hlp.congr'
    exact Eventually.of_forall fun n => by
      apply eLpNorm_congr_ae
      filter_upwards [(hz n i).2 β'] with x hx
      change (z n).2 i β' x - Z.2 i β' x =
        iterWeakPartial 2 j β (P (z n).1 i) V x - v j β x
      simpa only [v, dif_pos hj] using congrArg (fun r : ℝ => r - Z.2 i β' x) hx
  obtain ⟨hU, hUjet⟩ := MemWkp_of_iter_tendsto_eLpNorm hp hV k
    (fun n => (hz n i).1) v hv ht
  have hL2 : Tendsto (fun n => eLpNorm
      (fun x => P (z n).1 i x - v 0 ![] x) 2 (volume.restrict V)) atTop (𝓝 0) := by
    simpa only [iterWeakPartial_zero] using ht 0 ![] (Nat.zero_le k)
  have hpoint : ∀ᵐ x ∂volume.restrict V,
      Tendsto (fun n => P (z n).1 i x) atTop (𝓝 (P Z.1 i x)) :=
    Eventually.of_forall fun x => (hP i x).continuousAt.tendsto.comp hvalue
  have heq : P Z.1 i =ᵐ[volume.restrict V] v 0 ![] :=
    ae_eq_of_l2_limit_of_ae_pointwise_limit
      (fun n => (hz n i).1.memLp.aestronglyMeasurable)
      hU.memLp.aestronglyMeasurable hL2 hpoint
  refine ⟨(MemWkp_congr_ae hp hV heq).mpr hU, ?_⟩
  intro β
  have hj : β.1.1 ≤ k := Nat.le_of_lt_succ β.1.2
  have hactual := (iterWeakPartial_ae_congr hp hV β.1.1 β.2 heq).trans
    (hUjet β.1.1 β.2 hj)
  have hvβ : v β.1.1 β.2 = (Z.2 i β : E3 → ℝ) := by
    simp only [v, dif_pos hj]
  rw [hvβ] at hactual
  exact hactual.symm

/-- Completeness is inherited from the actual closed graph, after its
closedness proof above. -/
theorem weakSobolevGraph_completeSpace [CompleteSpace X]
    (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ))
    (hP : ∀ i : I, ∀ x : E3, Continuous (fun f : X => P f i x)) :
    CompleteSpace (weakSobolevGraph V hV k P) :=
  (weakSobolevGraph_isClosed V hV k P hP).completeSpace_coe

/-- The continuous first projection is the literal function coordinate.
Injectivity is the substantive derivative-identity theorem above. -/
def weakSobolevGraphValue (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) : weakSobolevGraph V hV k P →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X (WeakSobolevJetFamily I V k)).comp
    (weakSobolevGraph V hV k P).subtypeL

@[simp] theorem weakSobolevGraphValue_apply (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) (z : weakSobolevGraph V hV k P) :
    weakSobolevGraphValue V hV k P z = z.1.1 := rfl

/-- A block is constructed directly from the actual weak derivatives,
using their genuine L2 membership. -/
def weakSobolevJetBlockOfMem (V : Set E3) (k : ℕ)
    {u : E3 → ℝ} (hu : MemWkp k 2 u V) : WeakSobolevJetBlock V k :=
  WithLp.toLp 1 (fun β : WeakSobolevJetIndex k =>
    (iterWeakPartial_memLp_of_memWkp (hu.le_of_le (Nat.le_of_lt_succ β.1.2)) β.2).toLp
      (iterWeakPartial 2 β.1.1 β.2 u V))

theorem weakSobolevJetBlockOfMem_ae (V : Set E3) (k : ℕ)
    {u : E3 → ℝ} (hu : MemWkp k 2 u V) (β : WeakSobolevJetIndex k) :
    (weakSobolevJetBlockOfMem V k hu β : E3 → ℝ) =ᵐ[volume.restrict V]
      iterWeakPartial 2 β.1.1 β.2 u V :=
  (iterWeakPartial_memLp_of_memWkp (hu.le_of_le (Nat.le_of_lt_succ β.1.2)) β.2).coeFn_toLp

/-- The finite L1 block norm is exactly the real actual weak Sobolev norm;
this is why no hidden coordinate-count factor is used by the graph norm. -/
theorem weakSobolevJetBlockOfMem_norm (V : Set E3) (k : ℕ)
    {u : E3 → ℝ} (hu : MemWkp k 2 u V) :
    ‖weakSobolevJetBlockOfMem V k hu‖ = (iteratedWeakSobolevNorm k 2 u V).toReal := by
  classical
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
  have hnorm (β : WeakSobolevJetIndex k) :
      ‖weakSobolevJetBlockOfMem V k hu β‖ =
        (eLpNorm (iterWeakPartial 2 β.1.1 β.2 u V) 2 (volume.restrict V)).toReal := by
    exact Lp.norm_toLp _
      (iterWeakPartial_memLp_of_memWkp (hu.le_of_le (Nat.le_of_lt_succ β.1.2)) β.2)
  simp_rw [hnorm]
  rw [← ENNReal.toReal_sum (fun β _ =>
    (iterWeakPartial_memLp_of_memWkp (hu.le_of_le (Nat.le_of_lt_succ β.1.2)) β.2).eLpNorm_ne_top)]
  congr 1
  rw [Fintype.sum_sigma, wkpNorm_eq_sum]
  exact Fin.sum_univ_eq_sum_range
    (fun j => ∑ β : Fin j → Fin 3, eLpNorm (iterWeakPartial 2 j β u V) 2 (volume.restrict V))
    (k + 1)

/-- Every member's block is the actual weak-jet block of its own value,
and the graph norm controls that entire local weak Sobolev norm. -/
theorem weakSobolevGraph_local_norm_le (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) (z : weakSobolevGraph V hV k P) (i : I) :
    (iteratedWeakSobolevNorm k 2 (P z.1.1 i) V).toReal ≤ ‖z‖ := by
  have he : z.1.2 i = weakSobolevJetBlockOfMem V k (z.2 i).1 := by
    apply PiLp.ext
    intro β
    apply Lp.ext
    exact ((z.2 i).2 β).trans (weakSobolevJetBlockOfMem_ae V k (z.2 i).1 β).symm
  rw [← weakSobolevJetBlockOfMem_norm V k (z.2 i).1, ← he]
  exact (lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) z.1.2 i).trans
    (norm_snd_le z.1)

/-- Construct a graph element from one given value and proved actual weak
Sobolev bounds. There is no free choice of a derivative representative. -/
def weakSobolevGraphOfBound (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) (f : X)
    (hu : ∀ i : I, MemWkp k 2 (P f i) V)
    (S : ℝ) (hS : ∀ i : I, (iteratedWeakSobolevNorm k 2 (P f i) V).toReal ≤ S) :
    weakSobolevGraph V hV k P := by
  let z₀ : I → WeakSobolevJetBlock V k := fun i => weakSobolevJetBlockOfMem V k (hu i)
  have hz₀ : Memℓp z₀ ⊤ := memℓp_infty ⟨S, by
    rintro _ ⟨i, rfl⟩
    change ‖weakSobolevJetBlockOfMem V k (hu i)‖ ≤ S
    rw [weakSobolevJetBlockOfMem_norm]
    exact hS i⟩
  let z : WeakSobolevJetFamily I V k := ⟨z₀, hz₀⟩
  exact ⟨(f, z), fun i => ⟨hu i, weakSobolevJetBlockOfMem_ae V k (hu i)⟩⟩

@[simp] theorem weakSobolevGraphOfBound_value (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) (f : X)
    (hu : ∀ i : I, MemWkp k 2 (P f i) V)
    (S : ℝ) (hS : ∀ i : I, (iteratedWeakSobolevNorm k 2 (P f i) V).toReal ≤ S) :
    weakSobolevGraphValue V hV k P (weakSobolevGraphOfBound V hV k P f hu S hS) = f := rfl

theorem weakSobolevGraphOfBound_norm_le (V : Set E3) (hV : IsOpen V) (k : ℕ)
    (P : X →ₗ[ℝ] (I → E3 → ℝ)) (f : X)
    (hu : ∀ i : I, MemWkp k 2 (P f i) V)
    (S : ℝ) (hSnonneg : 0 ≤ S)
    (hS : ∀ i : I, (iteratedWeakSobolevNorm k 2 (P f i) V).toReal ≤ S) :
    ‖weakSobolevGraphOfBound V hV k P f hu S hS‖ ≤ max ‖f‖ S := by
  apply max_le_max le_rfl
  apply lp.norm_le_of_forall_le hSnonneg
  intro i
  change ‖weakSobolevJetBlockOfMem V k (hu i)‖ ≤ S
  rw [weakSobolevJetBlockOfMem_norm]
  exact hS i

#print axioms weakSobolevGraph_fst_injective
#print axioms weakSobolevGraph_isClosed
#print axioms weakSobolevGraph_completeSpace
#print axioms weakSobolevJetBlockOfMem_norm
#print axioms weakSobolevGraphOfBound_norm_le

end Yamabe3.Analysis.UniformElliptic
