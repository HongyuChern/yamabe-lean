import Yamabe3.Analysis.SpectralIntegralLinearity
import Yamabe3.Analysis.BanachFutureLinearity
import Yamabe3.Analysis.NativeIntegralAngularInverse
import Yamabe3.Analysis.NativeAngularLowOperator
import Yamabe3.Analysis.NativeAngularProjections

/-!
# The same actual native inverses as continuous linear maps

The native Hilbert basis and its inverse are used as genuine linear
isometries. Continuous linear maps on time curves transport the already
constructed high and low Banach fixed points. No new solution is selected.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory PoincareMT
open scoped Topology lp ContDiff BoundedContinuousFunction RealInnerProductSpace
namespace Yamabe3.Analysis.Delaunay
open Yamabe3.Analysis.SphereSpectrum

def angularCoordinatesCLM : (ℝ →ᵇ AngularL2) →L[ℝ] (ℝ →ᵇ SpectralSpace AngularIndex) :=
  angularBasis.repr.toLinearIsometry.toContinuousLinearMap.compLeftContinuousBounded ℝ

def angularSynthesisCLM : (ℝ →ᵇ SpectralSpace AngularIndex) →L[ℝ] (ℝ →ᵇ AngularL2) :=
  angularBasis.repr.symm.toLinearIsometry.toContinuousLinearMap.compLeftContinuousBounded ℝ

theorem angularCoordinatesCLM_apply (F : ℝ →ᵇ AngularL2) :
    angularCoordinatesCLM F = angularSourceCoordinates F := by
  apply BoundedContinuousFunction.ext
  intro t
  rfl

theorem angularSynthesisCLM_norm_le (U : ℝ →ᵇ SpectralSpace AngularIndex) :
    ‖angularSynthesisCLM U‖ ≤ ‖U‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg U)).mpr
  intro t
  change ‖angularBasis.repr.symm (U t)‖ ≤ ‖U‖
  simpa only [LinearIsometryEquiv.norm_map] using U.norm_coe_le_norm t

def nativeProjectedSourceCLM (p : AngularIndex → Prop) :
    (ℝ →ᵇ AngularL2) →L[ℝ] (ℝ →ᵇ AngularL2) :=
  (nativeAngularProjection p).compLeftContinuousBounded ℝ

theorem nativeProjectedSourceCLM_apply (p : AngularIndex → Prop) (F : ℝ →ᵇ AngularL2) :
    nativeProjectedSourceCLM p F = nativeProjectedSource p F := by
  apply BoundedContinuousFunction.ext
  intro t
  rfl

/-- This map is extensionally the already constructed native high inverse. -/
def nativeIntegralAngularInverseCLM {δ κ : ℝ} (hδ : |δ| < 5 / 2)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ) :
    (ℝ →ᵇ AngularL2) →L[ℝ] (ℝ →ᵇ AngularL2) :=
  angularSynthesisCLM.comp
    ((spectralIntegralPotentialInverseCLM nativeAngularRate (by norm_num)
      nativeAngularRate_lower hδ hκ0 hκ1 V hV).comp angularCoordinatesCLM)

theorem nativeIntegralAngularInverseCLM_apply {δ κ : ℝ} (hδ : |δ| < 5 / 2)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (V : ℝ →ᵇ ℝ)
    (hV : ∀ t, (∫ s : ℝ, spectralMajorant (5 / 2) δ s * |V (t - s)|) ≤ κ)
    (F : ℝ →ᵇ AngularL2) :
    nativeIntegralAngularInverseCLM hδ hκ0 hκ1 V hV F =
      nativeIntegralAngularInverse hδ hκ0 hκ1 V hV F := by
  apply BoundedContinuousFunction.ext
  intro t
  change angularBasis.repr.symm
      (spectralIntegralPotentialInverse nativeAngularRate (by norm_num)
        nativeAngularRate_lower hδ hκ0 hκ1 V hV (angularCoordinatesCLM F) t) = _
  rw [angularCoordinatesCLM_apply]
  rfl

/-- The native low inverse uses precisely the actual future Banach fixed point. -/
def nativeLowAngularInverseCLM (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (k : ℝ) (hk : 0 < k) (hgap : 7 / 2 < k ^ 2) :
    (ℝ →ᵇ AngularL2) →L[ℝ] (ℝ →ᵇ AngularL2) :=
  angularSynthesisCLM.comp
    ((banachFuturePotentialInverseCLM k hk (lowAngularOperatorBCF v hv hb)
      ((lowAngularOperatorBCF_norm_le v hv hb).trans_lt hgap)).comp angularCoordinatesCLM)

theorem nativeLowAngularInverseCLM_apply (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {k : ℝ} (hk : 0 < k) (hgap : 7 / 2 < k ^ 2)
    (F : ℝ →ᵇ AngularL2) (t : ℝ) :
    nativeLowAngularInverseCLM v hv hb k hk hgap F t =
      angularBasis.repr.symm (banachFuturePotentialInverse k hk (lowAngularOperatorBCF v hv hb)
        ((lowAngularOperatorBCF_norm_le v hv hb).trans_lt hgap) (angularSourceCoordinates F) t) := by
  change angularBasis.repr.symm (banachFuturePotentialInverse k hk (lowAngularOperatorBCF v hv hb)
    ((lowAngularOperatorBCF_norm_le v hv hb).trans_lt hgap) (angularCoordinatesCLM F) t) = _
  rw [angularCoordinatesCLM_apply]

theorem nativeLowAngularInverseCLM_norm_le (v : ℝ → ℝ) (hv : Continuous v)
    (hb : ∀ t, 0 ≤ v t ∧ v t ≤ 1) {k : ℝ} (hk : 0 < k) (hgap : 7 / 2 < k ^ 2)
    (F : ℝ →ᵇ AngularL2) :
    ‖nativeLowAngularInverseCLM v hv hb k hk hgap F‖ ≤ ‖F‖ / (k ^ 2 - 7 / 2) := by
  let A := lowAngularOperatorBCF v hv hb
  have hAn : ‖A‖ ≤ 7 / 2 := lowAngularOperatorBCF_norm_le v hv hb
  have hAg : ‖A‖ < k ^ 2 := hAn.trans_lt hgap
  have hbound : ‖banachFuturePotentialInverse k hk A hAg (angularSourceCoordinates F)‖ ≤
      ‖F‖ / (k ^ 2 - 7 / 2) := by
    calc
      _ ≤ ‖angularSourceCoordinates F‖ / (k ^ 2 - ‖A‖) :=
        banachFuturePotentialInverse_norm_le hk A hAg _
      _ ≤ ‖angularSourceCoordinates F‖ / (k ^ 2 - 7 / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hgap) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right (angularSourceCoordinates_norm_le F) (sub_pos.mpr hgap).le
  apply (BoundedContinuousFunction.norm_le (div_nonneg (norm_nonneg F) (sub_pos.mpr hgap).le)).mpr
  intro t
  rw [nativeLowAngularInverseCLM_apply, LinearIsometryEquiv.norm_map]
  exact (BoundedContinuousFunction.norm_coe_le_norm _ t).trans hbound

end Yamabe3.Analysis.Delaunay
