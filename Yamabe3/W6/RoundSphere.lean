import Yamabe3.Geometry.RoundStereographicDiffeomorph

/-!
# The actual unit three-sphere, without curvature dependencies

This is the same subtype of the four-dimensional Euclidean space as the
pinned `PoincareMT.UnitThreeSphere`.  Its native smooth atlas is inherited
from Mathlib; no new geometric structure or assumption is introduced.
-/

namespace Yamabe3.W6

/-- The unit sphere in the actual four-dimensional Euclidean space. -/
abbrev Sphere := Geometry.RoundStereographicSphere 3

end Yamabe3.W6
