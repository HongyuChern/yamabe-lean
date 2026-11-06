import Yamabe3.Analysis.Sphere.NativeSphereHeight

/-!
# Actual first-order lowering functions on the round sphere

The height derivative is the ambient linear functional applied to the real
inclusion differential.  This identifies a nonzero lowered function at any
point where the original function is nonzero, without assuming a spherical
harmonic decomposition.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareMT
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

namespace Yamabe3.Analysis.SphereSpectrum

open Poincare.Geometry.Riemannian.SpaceForm

local instance sphereDimensionLowering (n : ℕ) :
    Fact (Module.finrank ℝ (Ambient n) = n + 1) := ⟨by simp [Ambient]⟩

theorem mvfderiv_height {n : ℕ} (a : Ambient n) (x : UnitSphere n)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (height a) x v = inner ℝ a
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (Subtype.val : UnitSphere n → Ambient n) x v) := by
  have hF : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞
      (Subtype.val : UnitSphere n → Ambient n) := contMDiff_coe_sphere
  have ha : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞
      ((innerSL ℝ a) : Ambient n → ℝ) := (innerSL ℝ a).contDiff.contMDiff
  have hc := mfderiv_comp x (ha.mdifferentiable (by simp) (x : Ambient n))
    (hF.mdifferentiable (by simp) x)
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (height a) x = _ at hc
  rw [mfderiv_eq_fderiv, (innerSL ℝ a).fderiv] at hc
  simp +instances only [mvfderiv, hc, NormedSpace.fromTangentSpace]
  rfl

theorem inner_gradient_height {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    (f : UnitSphere n → ℝ) (a : Ambient n) (x : UnitSphere n) :
    (roundSphereMetric n).inner x (D.gradient f x) (D.gradient (height a) x) =
      inner ℝ a (mfderiv (𝓡 n) (𝓡 (n + 1))
        (Subtype.val : UnitSphere n → Ambient n) x (D.gradient f x)) := by
  rw [(roundSphereMetric n).symm, D.inner_gradient, mvfderiv_height]

def lowering {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    (f : UnitSphere n → ℝ) (α : ℝ) (a : Ambient n) (x : UnitSphere n) : ℝ :=
  (roundSphereMetric n).inner x (D.gradient f x) (D.gradient (height a) x) +
    α * height a x * f x

theorem lowering_self {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    (f : UnitSphere n → ℝ) (α : ℝ) (x : UnitSphere n) :
    lowering D f α (x : Ambient n) x = α * f x := by
  rw [lowering, inner_gradient_height, sphere_normal_tangent]
  have hx : height (x : Ambient n) x = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere x)
  rw [hx]
  ring

theorem exists_lowering_ne_zero {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    {f : UnitSphere n → ℝ} {α : ℝ} (hα : α ≠ 0) (hf : ∃ x, f x ≠ 0) :
    ∃ a : Ambient n, ∃ x : UnitSphere n, lowering D f α a x ≠ 0 := by
  obtain ⟨x, hx⟩ := hf
  refine ⟨(x : Ambient n), x, ?_⟩
  rw [lowering_self]
  exact mul_ne_zero hα hx

theorem smooth_inner_gradients {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient f x) (D.gradient h x)) := by
  intro x
  have h := ((g.contMDiff x).clm_bundle_apply (D.contMDiffAt_gradient (hf x))).clm_bundle_apply
    (D.contMDiffAt_gradient (hh x))
  simpa using (Bundle.contMDiffAt_totalSpace.mp h).2

theorem smooth_lowering {n : ℕ} (D : LeviCivitaData (roundSphereMetric n))
    {f : UnitSphere n → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (α : ℝ) (a : Ambient n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (lowering D f α a) :=
  (smooth_inner_gradients D hf (smooth_height a)).add
    ((contMDiff_const.mul (smooth_height a)).mul hf)

#print axioms mvfderiv_height
#print axioms exists_lowering_ne_zero
#print axioms smooth_lowering

end Yamabe3.Analysis.SphereSpectrum
