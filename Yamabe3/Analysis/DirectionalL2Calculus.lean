import Yamabe3.Analysis.DirectionalEllipticRegularity

/-! Single-direction L2 weak calculus on a precompact open set. This
retains actual derivative witnesses without assuming all first derivatives. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
namespace Yamabe3.Analysis.UniformElliptic
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryLocalization
open Poincare.Analysis.Elliptic.Iteration
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def DirectionalL2 (k : Fin d) (f : E → ℝ) (O : Set E) : Prop :=
  MemLp f 2 (volume.restrict O) ∧ ∃r : E → ℝ,
    MemLp r 2 (volume.restrict O) ∧ HasWeakPartialDeriv k r f O

theorem directionalL2_of_memW1p {O : Set E} {f : E → ℝ}
    (hf : MemW1p 2 f O) (k : Fin d) : DirectionalL2 k f O := ⟨hf.1,hf.2 k⟩

theorem DirectionalL2.add {O : Set E} {k : Fin d} {f g : E → ℝ}
    (hf : DirectionalL2 k f O) (hg : DirectionalL2 k g O) :
    DirectionalL2 k (fun x => f x+g x) O := by
  obtain ⟨hf,r,hr,hwr⟩ := hf
  obtain ⟨hg,s,hs,hws⟩ := hg
  refine ⟨hf.add hg,fun x => r x+s x,hr.add hs,?_⟩
  intro φ hφ hc ht
  have hφL : MemLp φ 2 (volume.restrict O) := (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hDL : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single k 1)) 2 (volume.restrict O) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).restrict O
  have ha := integral_add (hf.integrable_mul hDL) (hg.integrable_mul hDL)
  have hb := integral_add (hr.integrable_mul hφL) (hs.integrable_mul hφL)
  simp only [Pi.mul_apply] at ha hb
  simp only [add_mul]
  rw [ha,hb,hwr φ hφ hc ht,hws φ hφ hc ht]
  ring

theorem DirectionalL2.smooth_mul {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {k : Fin d} {f a : E → ℝ} (hf : DirectionalL2 k f O) (ha : ContDiff ℝ ∞ a) :
    DirectionalL2 k (fun x => a x*f x) O := by
  obtain ⟨hf,r,hr,hw⟩ := hf
  have hm {v c : E → ℝ} (hv : MemLp v 2 (volume.restrict O)) (hc : ContDiff ℝ ∞ c) :
      MemLp (fun x => c x*v x) 2 (volume.restrict O) :=
    memWkp_mul_smooth_of_isCompact_closure 0 hO hOc hv hc
  have hda := contDiff_partial ha k
  refine ⟨hm hf ha,fun x => a x*r x+partialDeriv k a x*f x,
    (hm hr ha).add (hm hf hda),?_⟩
  exact hw.mul_smooth hO ha (hf.locallyIntegrable (by norm_num)) (hr.locallyIntegrable (by norm_num))

theorem DirectionalL2.sum {O : Set E} {k : Fin d} {ι : Type*}
    (s : Finset ι) {f : ι → E → ℝ} (hf : ∀i∈s,DirectionalL2 k (f i) O) :
    DirectionalL2 k (fun x => ∑i∈s,f i x) O := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨by simp,0,by simp,?_⟩
    intro φ _ _ _
    simp
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self a s)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

#print axioms directionalL2_of_memW1p
#print axioms DirectionalL2.add
#print axioms DirectionalL2.smooth_mul
#print axioms DirectionalL2.sum
end Yamabe3.Analysis.UniformElliptic
