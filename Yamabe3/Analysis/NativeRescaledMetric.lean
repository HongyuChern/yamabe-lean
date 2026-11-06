import Yamabe3.Analysis.NativeWeakDivergenceJacobian
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension

/-! The rescaled coefficient field is itself a genuine smooth positive
metric, including scale zero. Its native density and divergence matrix
are exactly the previously retained rescaled ones, with no scale loss. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Filter PoincareMT
open scoped Manifold ContDiff Topology
namespace Yamabe3.Analysis.UniformElliptic
open PoincareMT.LeviCivitaData.Dirichlet
local notation "E" => EuclideanSpace ℝ (Fin 3)

def nativeRescaledMetric (g : RiemannianMetric 3 E) (r : ℝ) : RiemannianMetric 3 E :=
  RiemannianMetric.ofEuclideanCoefficients (fun x => g.euclideanCoefficients (r • x))
    ((contDiff_iff_contDiffAt.mpr (g.contDiffAt_euclideanCoefficients)).comp (contDiff_id.const_smul r))
    (fun x v w => g.symm (r • x) v w) (fun x v hv => g.pos (r • x) v hv)

theorem nativeRescaledMetric_inner (g : RiemannianMetric 3 E) (r : ℝ) (x v w : E) :
    (nativeRescaledMetric g r).inner x v w=g.inner (r • x) v w := rfl

theorem nativeRescaledMetric_coefficients (g : RiemannianMetric 3 E) (r : ℝ) (x : E) :
    (nativeRescaledMetric g r).pullbackCoefficients id x=g.pullbackCoefficients id (r • x) := by
  ext v w
  change (nativeRescaledMetric g r).inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
    (mfderiv (𝓡 3) (𝓡 3) id x w)=
      g.inner (r • x) (mfderiv (𝓡 3) (𝓡 3) id (r • x) v) (mfderiv (𝓡 3) (𝓡 3) id (r • x) w)
  simp only [mfderiv_id,nativeRescaledMetric_inner]
  rfl

theorem nativeRescaledMetric_density (g : RiemannianMetric 3 E) (r : ℝ) (x : E) :
    (nativeRescaledMetric g r).pullbackVolumeDensity id x=g.pullbackVolumeDensity id (r • x) := by
  simp only [RiemannianMetric.pullbackVolumeDensity,mfderiv_id,ContinuousLinearMap.id_apply,id_eq,
    nativeRescaledMetric_inner]

theorem nativeRescaledMetric_divergenceMatrix (g : RiemannianMetric 3 E) (r : ℝ) :
    nativeDivergenceMatrix (nativeRescaledMetric g r)=nativeScaledDivergenceMatrix g r := by
  funext x
  ext i j
  change (nativeRescaledMetric g r).pullbackVolumeDensity id x*
    EuclideanSpace.proj i (((nativeRescaledMetric g r).pullbackCoefficients id x).inverse (EuclideanSpace.proj j))=
      g.pullbackVolumeDensity id (r • x)*
        EuclideanSpace.proj i ((g.pullbackCoefficients id (r • x)).inverse (EuclideanSpace.proj j))
  rw [nativeRescaledMetric_density,nativeRescaledMetric_coefficients]

#print axioms nativeRescaledMetric_inner
#print axioms nativeRescaledMetric_coefficients
#print axioms nativeRescaledMetric_density
#print axioms nativeRescaledMetric_divergenceMatrix
end Yamabe3.Analysis.UniformElliptic
