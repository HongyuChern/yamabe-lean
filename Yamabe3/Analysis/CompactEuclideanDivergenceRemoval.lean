import Yamabe3.Analysis.CompactDivergenceRemoval
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! The countable-exception divergence identity transported to the
actual Euclidean volume and orthonormal coordinate vectors. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory Metric
open scoped Topology
namespace Yamabe3.Analysis.UniformElliptic
local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "P" => (Fin 3→ℝ)

theorem integral_compact_euclidean_divergence_off_countable
    {Z:E→P} (hZ:Continuous Z) (hc:HasCompactSupport Z)
    {s:Set E} (hs:s.Countable) (hd:∀x∉s,DifferentiableAt ℝ Z x)
    (hi:Integrable (fun x:E=>∑i:Fin 3,fderiv ℝ Z x (EuclideanSpace.single i 1) i)) :
    (∫x:E,∑i:Fin 3,fderiv ℝ Z x (EuclideanSpace.single i 1) i)=0 := by
  let e:=EuclideanSpace.equiv (Fin 3) ℝ
  let f:P→P:=Z ∘ e.symm
  let D:E→ℝ:=fun x=>∑i:Fin 3,fderiv ℝ Z x (EuclideanSpace.single i 1) i
  have he(x:P):(∑i:Fin 3,fderiv ℝ f x (Pi.single i 1) i)=D (e.symm x) := by
    dsimp only [f]
    rw [e.symm.comp_right_fderiv]
    rfl
  have hmeas:= (MeasurableEquiv.toLp 2 (Fin 3→ℝ)).measurableEmbedding
  have hm:=PiLp.volume_preserving_toLp (Fin 3)
  have hit:Integrable (fun x:P=>D (e.symm x)) := (hm.integrable_comp_emb hmeas).mpr hi
  have hfint:Integrable (fun x:P=>∑i:Fin 3,fderiv ℝ f x (Pi.single i 1) i) := by
    simpa only [he] using hit
  have hzero:=integral_compact_divergence_off_countable (hZ.comp e.symm.continuous)
    (hc.comp_homeomorph e.symm.toHomeomorph) (hs.preimage e.symm.injective)
    (fun x hx=>(hd (e.symm x) hx).comp x e.symm.differentiableAt) hfint
  change (∫x:P,∑i:Fin 3,fderiv ℝ f x (Pi.single i 1) i)=0 at hzero
  simp only [he] at hzero
  have heint:(∫x:P,D (e.symm x))=∫x:E,D x:=hm.integral_comp hmeas D
  exact heint.symm.trans hzero

#print axioms integral_compact_euclidean_divergence_off_countable
end Yamabe3.Analysis.UniformElliptic
