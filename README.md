# Singular Yamabe geometry in Lean

This Lean 4 package formalizes the two-point singular Yamabe theorem on the round three-sphere, the positive Green function on a closed connected positive-Yamabe three-manifold, a completeness criterion for cylindrical ends, and a linear gluing theorem on a specified weighted source space.

For the broader singular Yamabe problem motivating this development, see the preprint by Hongyu Chen and Li Ma. [*Complete conformal metrics of constant positive scalar curvature with prescribed isolated singularities* (arXiv:2610.31058)](https://arxiv.org/abs/2610.31058)

The project aims to formalize the existence theorem of the preprint, starting with dimension three. In dimension three, the target covers every smooth closed connected manifold with positive Yamabe constant and every prescribed finite set of at least two points. Version 0.1.0 is the first stage of this work and contains the round three-sphere two-point theorem and the results described below.

## The singular Yamabe equation on the round three-sphere with two prescribed points

**Theorem.** Let $g$ be the unit round metric on $S^3$. For any two distinct points $p,q\in S^3$, there exists a smooth positive function $u$ on $S^3\setminus\{p,q\}$ such that $u^4g$ is complete and has constant scalar curvature $6$. With $\Delta_g=\operatorname{div}_g\nabla_g$, the function $u$ satisfies

$$
-8\Delta_g u+6u=6u^5\qquad\text{on }S^3\setminus\{p,q\}.
$$

The Lean theorem also records that the intrinsic distance between any two points is finite and that every initial position and velocity admits a smooth geodesic defined on all of $\mathbb R$.

The Lean proof constructs the cylindrical solution $v(x)=3^{-1/4}|x|^{-1/2}$ on $\mathbb R^3\setminus\{0\}$. It pulls back the metric $v^4g_{\mathrm{Eucl}}$ by stereographic projection from $p$ followed by the translation that sends the image of $q$ to the origin. In cylindrical coordinates, the conformal factor is the constant member of the Fowler family. [Korevaar, Mazzeo, Pacard, and Schoen, *Refined asymptotics for constant scalar curvature metrics with isolated singularities* (1999), §2](https://perso.pages.math.cnrs.fr/users/frank.pacard/Publications/25.pdf#page=5)

Mazzeo and Pacard's Theorem 1 gives a gluing construction on the round sphere for prescribed finite singular sets of at least two points. They credit Schoen with the earlier construction. [Schoen, *The existence of weak solutions with prescribed singular behavior for a conformally invariant scalar equation* (1988)](https://doi.org/10.1002/cpa.3160410305) · [Mazzeo and Pacard, *Constant scalar curvature metrics with isolated singularities* (1999), Theorem 1](https://perso.pages.math.cnrs.fr/users/frank.pacard/Publications/26.pdf#page=2)

The formalized existence theorem covers sets of exactly two points. A separate transport theorem applies to any finite set $\Lambda$ and any smooth conformal diffeomorphism $F\colon M\to N$ of three-manifolds. If $N\setminus F(\Lambda)$ already carries a complete singular Yamabe metric of scalar curvature $6$ with finite intrinsic distances and a global smooth geodesic for every initial position and velocity, the theorem pulls it back to $M\setminus\Lambda$ with the same properties.

The completeness argument also yields a criterion for general conformal factors on $\mathbb R^3\setminus\{0\}$. If a smooth positive function $u$ satisfies $u(x)^2\ge c/|x|$ everywhere for some $c>0$, then $u^4g_{\mathrm{Eucl}}$ is complete.

| Result | Lean declaration |
| --- | --- |
| Round sphere with any two distinct prescribed points | [`Yamabe3.W6.round_card_two_conclusion`](Yamabe3/W6/TwoPointComplete.lean#L88) |
| Two-point existence given a conformal diffeomorphism to the round sphere | [`Yamabe3.W6.conformal_round_card_two_conclusion`](Yamabe3/W6/TwoPointComplete.lean#L100) |
| Conformal transport of a given solution across a finite puncture set | [`Yamabe3.Geometry.puncturedConclusion_conformal_transport`](Yamabe3/Geometry/SphericalPuncturedTransport.lean#L112) |
| Completeness under a cylindrical lower bound | [`Yamabe3.W6.euclidean_cylindrical_complete`](Yamabe3/W6/EuclideanCylinder.lean#L133) |

## Green functions and completeness

On a smooth closed connected three-manifold with positive Yamabe constant, the Green function family for $-\Delta_g+R_g/8$ is normalized by $4\pi\delta_p$, positive away from the pole, and symmetric off the diagonal. In a normal Gauss chart, a separate theorem gives the inverse-radius singular term and weighted bounds on the remainder and its first two derivatives.

The cylindrical completeness theorem applies to a smooth positive solution with the stipulated Gauss charts and cutoffs at finitely many ends. In each chart it uses a bound of the form $u^2 \ge c/r$ for small $r$. It obtains metric and geodesic completeness for the metric defined by that same solution.

| Result | Lean declaration |
| --- | --- |
| Positive symmetric Green family and smooth-test identities | [`Yamabe3.Analysis.GreenParametrix.full_smooth_test_green_family`](Yamabe3/Analysis/Green/NativeGreenFullTests.lean#L34) |
| Green function expansion at a pole | [`Yamabe3.Analysis.GreenParametrix.exists_native_green_with_C2_expansion`](Yamabe3/Analysis/Green/NativeGreenC2Expansion.lean#L33) |
| Finite cylindrical ends and the original PDE solution | [`Yamabe3.Target.puncturedConclusion_of_cylindrical_solution`](Yamabe3/Target/CylindricalAssembly.lean#L20) |

## Linear gluing in the original metric

The linear theorem takes a source in the single-chart weighted `HalfEndPhysicalH2SourceGraph`. Its assumptions include the chart and normalization data and a Delaunay phase satisfying the stated spectral bound. It produces one field satisfying the interior and exterior equations and the assembled weak equation. The exterior equation uses the smooth truncated potential specified by the theorem. Conormal matching in the calibrated trace quotient holds under the Gauss identity and the stated upper bound on the volume density along the matching sphere. The construction retains the computed low-mode corrections. The entrance $H^4$ bound is stated for each fixed physical scale. The Lean signature lists the precise coefficient, source, and geometric assumptions.

The entry point is [`Yamabe3.Analysis.SpherePolar.exists_nativeOriginal_scoped_linear_full_closure`](Yamabe3/Analysis/NativeOriginalScopedLinearFullProducer.lean#L41). Its mathematical scope is the stated linear source problem and boundary data.

## Build and inspect the statements

Install [Elan](https://github.com/leanprover/elan). The files `lean-toolchain` and `lake-manifest.json` pin Lean 4.33.1 and the dependency revisions.

```sh
lake exe cache get
lake build
lake env lean Verify.lean
```

`import Yamabe3` imports the four developments. To build the round-sphere entry point alone, run `lake build +Yamabe3.W6.TwoPointComplete`. The verification file prints the six public statements and their axiom dependencies.

## Validation

The package was built from source in an isolated macOS arm64 workspace with Lean 4.33.1. The build used checkouts of the pinned dependency commits and official Mathlib dependency caches. The six statements in `Verify.lean` passed the type and axiom checks. Their reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The round three-sphere two-point theorem also passed Comparator on Linux. The
check compared the exported proof against the separately stated proposition and
replayed the proof in Lean and Nanoda. The proof revision and dependency pins
match this release. See the [Comparator files and result](verification/round-two-point/README.md).

## License

Original Lean source contributions are licensed under [Apache-2.0](LICENSE).
The [source notices](NOTICE.md) retain the relevant third-party notices, and
the [modification record](MODIFICATIONS.md) lists adapted code by file.

See [v0.1.0 release notes](CHANGELOG.md).
