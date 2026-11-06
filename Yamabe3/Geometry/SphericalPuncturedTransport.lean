import Yamabe3.Geometry.SphericalConformalTransport
import Yamabe3.Target.Statement

/-!
# Conformal transport with the literal prescribed finite puncture set

The restriction of the supplied ambient diffeomorphism is constructed here.
Its image puncture set is `Finset.map`, so no extra points, genericity, or
balancing conditions enter.  The final theorem transports the existing target
predicate; it does not assert the still-unproved round-sphere existence input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TopologicalSpace
open scoped Manifold ContDiff Bundle ENNReal

namespace Yamabe3.Geometry

open PoincareMT PoincareMT.MetricSurgery

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T3Space M] [T3Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

omit [T3Space M] [T3Space N] [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem mem_mapped_punctures_iff
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Λ : Finset M) (x : M) :
    F x ∈ Λ.map F.toEquiv.toEmbedding ↔ x ∈ Λ := by
  classical
  simp

/-- Restrict the actual ambient map to the exact finite-set complements. -/
def puncturedDiffeomorph
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Λ : Finset M) :
    Diffeomorph (𝓡 3) (𝓡 3) (Target.puncturedOpen Λ)
      (Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding)) ∞ := by
  classical
  let e : Target.puncturedOpen Λ ≃
      Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding) := {
    toFun := fun x => ⟨F x.val, fun hx => x.property
      ((mem_mapped_punctures_iff F Λ x.val).mp hx)⟩
    invFun := fun y => ⟨F.symm y.val, fun hy => y.property
      (Finset.mem_map.mpr ⟨F.symm y.val, hy, F.apply_symm_apply y.val⟩)⟩
    left_inv := fun x => Subtype.ext (F.symm_apply_apply x.val)
    right_inv := fun y => Subtype.ext (F.apply_symm_apply y.val) }
  refine { e with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff
      (Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding)) e).mp
    exact F.contMDiff.comp
      (contMDiff_subtype_val (I := 𝓡 3) (U := Target.puncturedOpen Λ) (n := ∞))
  · apply (ContMDiff.subtypeVal_comp_iff (Target.puncturedOpen Λ) e.symm).mp
    exact F.symm.contMDiff.comp (contMDiff_subtype_val (I := 𝓡 3)
      (U := Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding)) (n := ∞))

@[simp] theorem puncturedDiffeomorph_coe_apply
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Λ : Finset M)
    (x : Target.puncturedOpen Λ) :
    ((puncturedDiffeomorph F Λ x :
      Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding)) : N) = F (x : M) := rfl

/-- The derivative identity is proved by the chain rule for the two actual
open-submanifold inclusions. -/
theorem puncturedDiffeomorph_derivative_coe
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Λ : Finset M)
    (x : Target.puncturedOpen Λ) (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3)
      (Subtype.val : Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding) → N)
      (puncturedDiffeomorph F Λ x)
      (mfderiv (𝓡 3) (𝓡 3) (puncturedDiffeomorph F Λ) x v) =
    mfderiv (𝓡 3) (𝓡 3) F (x : M)
      (mfderiv (𝓡 3) (𝓡 3)
        (Subtype.val : Target.puncturedOpen Λ → M) x v) := by
  have hleft := mfderiv_comp x
    (((contMDiff_subtype_val (I := 𝓡 3)
      (U := Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding)) (n := ∞))
      (puncturedDiffeomorph F Λ x)).mdifferentiableAt (by simp))
    ((puncturedDiffeomorph F Λ).mdifferentiable (by simp) x)
  have hright := mfderiv_comp x (F.mdifferentiable (by simp) (x : M))
    (ContMDiffAt.mdifferentiableAt
      ((contMDiff_subtype_val (I := 𝓡 3) (U := Target.puncturedOpen Λ) (n := ∞)) x)
      (by simp))
  exact congrArg (fun L => L v) (hleft.symm.trans hright)

theorem conformal_pullback_restrict_punctures
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Λ : Finset M) (θ : M → ℝ)
    (hF : ∀ x v w, h.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
      (mfderiv (𝓡 3) (𝓡 3) F x w) = θ x ^ 4 * g.inner x v w)
    (x : Target.puncturedOpen Λ) (v w : TangentSpace (𝓡 3) x) :
    (restrictMetric h (Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding))).inner
      (puncturedDiffeomorph F Λ x)
      (mfderiv (𝓡 3) (𝓡 3) (puncturedDiffeomorph F Λ) x v)
      (mfderiv (𝓡 3) (𝓡 3) (puncturedDiffeomorph F Λ) x w) =
    θ (x : M) ^ 4 * (restrictMetric g (Target.puncturedOpen Λ)).inner x v w := by
  simp only [restrictMetric_inner]
  rw [puncturedDiffeomorph_derivative_coe F Λ x v,
    puncturedDiffeomorph_derivative_coe F Λ x w]
  exact hF x.val _ _

omit [T3Space M] [T3Space N] [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem mapped_punctures_card
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Λ : Finset M) :
    (Λ.map F.toEquiv.toEmbedding).card = Λ.card := Finset.card_map _

/-- The exact project target transports through actual ambient conformal
equivalence data.  Its only mathematical existence input is explicitly the
same target on the literal mapped puncture set. -/
theorem puncturedConclusion_conformal_transport
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Λ : Finset M) (θ : M → ℝ)
    (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ) (hθpos : ∀ x, 0 < θ x)
    (hF : ∀ x v w, h.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v)
      (mfderiv (𝓡 3) (𝓡 3) F x w) = θ x ^ 4 * g.inner x v w)
    (hs : Target.puncturedConclusion h (Λ.map F.toEquiv.toEmbedding)) :
    Target.puncturedConclusion g Λ := by
  obtain ⟨u, hu, hupos, heq, hc, hfinite, _⟩ := hs
  let Fp := puncturedDiffeomorph F Λ
  let θp : Target.puncturedOpen Λ → ℝ := fun x => θ x.val
  have hθp : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θp :=
    hθ.comp (contMDiff_subtype_val (I := 𝓡 3) (U := Target.puncturedOpen Λ) (n := ∞))
  have hθppos (x : Target.puncturedOpen Λ) : 0 < θp x := hθpos x.val
  let gp := restrictMetric g (Target.puncturedOpen Λ)
  let hp := restrictMetric h (Target.puncturedOpen (Λ.map F.toEquiv.toEmbedding))
  have hm : ∀ x v w, hp.inner (Fp x) (mfderiv (𝓡 3) (𝓡 3) Fp x v)
      (mfderiv (𝓡 3) (𝓡 3) Fp x w) = θp x ^ 4 * gp.inner x v w :=
    conformal_pullback_restrict_punctures g h F Λ θ hF
  let v : Target.puncturedOpen Λ → ℝ := fun x => θp x * u (Fp x)
  have hv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ v := hθp.mul (hu.comp Fp.contMDiff)
  have hvpos (x : Target.puncturedOpen Λ) : 0 < v x :=
    mul_pos (hθppos x) (hupos (Fp x))
  refine ⟨v, hv, hvpos, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (yamabe_equation_conformal_diffeomorph_iff gp hp Fp θp u hθp hu
      hθppos hupos hm x).mp (heq (Fp x))
  · exact (conformal_diffeomorph_final_complete_iff gp hp Fp θp u hθp hu
      hθppos hupos hm).mp hc
  · intro x y
    rw [← conformal_diffeomorph_final_edist gp hp Fp θp u hθp hu hθppos hupos hm x y]
    exact hfinite (Fp x) (Fp y)
  · intro x w
    exact conformal_diffeomorph_final_global_geodesic gp hp Fp θp u hθp hu
      hθppos hupos hm hc x w

/-- Changing the smooth positive background representative preserves the
full project conclusion for exactly the same specified finite point set. -/
theorem puncturedConclusion_change_representative_iff
    (g : RiemannianMetric 3 M) (Λ : Finset M) (θ : M → ℝ)
    (hθ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ θ) (hθpos : ∀ x, 0 < θ x) :
    Target.puncturedConclusion
      (positiveScaling g (fun x => θ x ^ 4) (hθ.pow 4)
        (fun x => pow_pos (hθpos x) 4)) Λ ↔
      Target.puncturedConclusion g Λ := by
  let F : Diffeomorph (𝓡 3) (𝓡 3) M M ∞ := Diffeomorph.refl (𝓡 3) M ∞
  let h := positiveScaling g (fun x => θ x ^ 4) (hθ.pow 4)
    (fun x => pow_pos (hθpos x) 4)
  have hmap : Λ.map F.toEquiv.toEmbedding = Λ := by
    ext x
    simp [F]
  constructor
  · intro hs
    apply puncturedConclusion_conformal_transport g h F Λ θ hθ hθpos
    · intro x v w
      simp [F, h, positiveScaling_inner]
    · simpa only [hmap] using hs
  · intro hs
    have hθinv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => (θ x)⁻¹) :=
      hθ.inv₀ (fun x => (hθpos x).ne')
    apply puncturedConclusion_conformal_transport h g F Λ
      (fun x => (θ x)⁻¹) hθinv (fun x => inv_pos.mpr (hθpos x))
    · intro x v w
      simp only [F, Diffeomorph.coe_refl, mfderiv_id]
      change g.inner x v w = (θ x)⁻¹ ^ 4 * (θ x ^ 4 * g.inner x v w)
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (hθpos x).ne']
      simp
    · simpa only [hmap] using hs

#print axioms puncturedDiffeomorph
#print axioms puncturedDiffeomorph_derivative_coe
#print axioms conformal_pullback_restrict_punctures
#print axioms puncturedConclusion_conformal_transport
#print axioms puncturedConclusion_change_representative_iff

end Yamabe3.Geometry
