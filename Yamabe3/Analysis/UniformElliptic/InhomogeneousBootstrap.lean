import Yamabe3.Analysis.UniformElliptic.LocalUniformJet
import PoincareLib.Analysis.Elliptic.Regularity.Iteration.Bootstrap
import PoincareLib.Analysis.Elliptic.Regularity.Sobolev.Embedding.SmoothRepresentative

/-!
# Actual smooth inhomogeneous elliptic bootstrap

The pinned gain-of-two proof already handles a genuine source. Adding the
actual smooth source to the zeroth-order bootstrap gives every local order.
Local source and potential smoothness are converted into the global smooth
extensions required by that proof, using real cutoffs and unchanged germs.
The L2 weak first derivatives remain explicit here and are constructed by
the finite-mode Caccioppoli limit in the application.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace Yamabe3.Analysis.UniformElliptic

open Poincare.Analysis.Elliptic
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memWkpLocally_all_of_weak_smooth_source [NeZero d]
    {O : Set E} (hO : IsOpen O)
    {A : E → Matrix (Fin d) (Fin d) ℝ} {Q F u : E → ℝ} {p : Fin d → E → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (heq : WeakEquation O (matrixFlux A p) (fun x => F x + Q x * u x)) :
    ∀ k, MemWkpLocally k u O := by
  have hFs (k : ℕ) : MemWkpLocally k F O := by
    apply locally_of_memWkp hO
    exact (MemWkp_of_smooth_compactSupport isOpen_univ hF hFc (subset_univ _)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) k).mono_set (by norm_num) hO (subset_univ _)
  intro k
  induction k with
  | zero => exact locally_of_memWkp hO hu
  | succ k ih =>
    exact (memWkpLocally_add_two_of_weakEquation k hO hA hpos hu hp hpartial
      ((hFs k).add (ih.smooth_mul hQ)) heq).mono_order (by omega)

/-- A genuine H1 weak solution with a genuine smooth source has a smooth
representative; no classical regularity is supplied as an extra field. -/
theorem exists_smooth_representative_of_weak_smooth_source (hd : 0 < d)
    {O : Set E} (hO : IsOpen O)
    {A : E → Matrix (Fin d) (Fin d) ℝ} {Q F u : E → ℝ} {p : Fin d → E → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (heq : WeakEquation O (matrixFlux A p) (fun x => F x + Q x * u x)) :
    ∃ U : E → ℝ, ContDiffOn ℝ ∞ U O ∧ U =ᵐ[volume.restrict O] u := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hreg := memWkpLocally_all_of_weak_smooth_source hO hA hpos hQ hF hFc hu hp hpartial heq
  apply Poincare.Analysis.Sobolev.EuclideanIteratedEmbedding.exists_smooth_representative_of_memWkp_locally
  intro x hx k
  exact hreg k x hx

/-- Local smooth potential and source are sufficient on a precompact
subdomain. Actual cutoff extensions are constructed before applying the
inhomogeneous gain-of-two proof. -/
theorem exists_smooth_representative_of_local_smooth_source (hd : 0 < d)
    {O V : Set E} (hO : IsOpen O) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    {A : E → Matrix (Fin d) (Fin d) ℝ} {Q F u : E → ℝ} {p : Fin d → E → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hpos : ∀ x ∈ V, (A x).PosDef)
    (hQ : ContDiffOn ℝ ∞ Q O) (hF : ContDiffOn ℝ ∞ F O)
    (hu : MemLp u 2 (volume.restrict V))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict V))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u V)
    (heq : WeakEquation V (matrixFlux A p) (fun x => F x + Q x * u x)) :
    ∃ U : E → ℝ, ContDiffOn ℝ ∞ U V ∧ U =ᵐ[volume.restrict V] u := by
  obtain ⟨Qe, hQe, -, hQeg⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hQ
  obtain ⟨Fe, hFe, hFec, hFeg⟩ := exists_smooth_compact_extension_near_compact hO hVc hVO hF
  apply exists_smooth_representative_of_weak_smooth_source hd hV hA hpos hQe hFe hFec
    hu hp hpartial
  intro φ hφ hφc hφV
  calc
    _ = ∫ x in V, (F x + Q x * u x) * φ x := heq φ hφ hφc hφV
    _ = ∫ x in V, (Fe x + Qe x * u x) * φ x := by
      apply setIntegral_congr_fun hV.measurableSet
      intro x hx
      dsimp only
      rw [(hQeg x (subset_closure hx)).self_of_nhds,
        (hFeg x (subset_closure hx)).self_of_nhds]

#print axioms memWkpLocally_all_of_weak_smooth_source
#print axioms exists_smooth_representative_of_local_smooth_source

end Yamabe3.Analysis.UniformElliptic
