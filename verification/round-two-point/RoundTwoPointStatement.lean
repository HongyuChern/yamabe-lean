import Yamabe3.Target.Statement
import Yamabe3.W6.RoundSphere
import PoincareLib.Topology.Manifold.Surgery.Event.Three.ThreeSphereMetric

namespace Yamabe3.ComparatorTargets

def RoundSphereTwoPoints : Prop :=
  ∀ (Λ : Finset W6.Sphere), Λ.card = 2 →
    Target.puncturedConclusion PoincareMT.M38.threeSphereMetric Λ

end Yamabe3.ComparatorTargets
