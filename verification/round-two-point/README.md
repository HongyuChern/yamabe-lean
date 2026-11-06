# Comparator check for the round three-sphere theorem

[RoundTwoPointStatement.lean](RoundTwoPointStatement.lean) fixes the proposition
independently of the proof module. [Challenge.lean](Challenge.lean) declares the
target with a proof placeholder. [Solution.lean](Solution.lean) supplies the
proof from `Yamabe3.W6.round_card_two_conclusion`. The
[configuration](comparator-round.json) restricts the solution to the axioms
`propext`, `Classical.choice`, and `Quot.sound`.

The [recorded result](result.txt) is from Ubuntu 24.04 on arm64 using Lean 4.33.1.
The proofs and dependency pins in this candidate match that run. Source notices
were added afterward.

To reproduce the check in a disposable copy of the project, use Linux with
a working user systemd service. Put `landrun` and `nanoda_bin` in `PATH`
using the revisions recorded below. Run these commands from the project root.

```sh
cp verification/round-two-point/*.lean .
cat >> lakefile.toml <<'LAKE'

[[lean_lib]]
name = "RoundTwoPointStatement"

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"
LAKE
lake exe cache get
lake build RoundTwoPointStatement Challenge Solution @Comparator/comparator @lean4export/lean4export
export PATH="$PWD/.lake/packages/Comparator/.lake/build/bin:$PWD/.lake/packages/lean4export/.lake/build/bin:$PATH"
mkdir -p "$PWD/.lake/comparator-tmp"
export TMPDIR="$PWD/.lake/comparator-tmp"
systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX --working-directory="$PWD" \
  -E PATH -E TMPDIR -- lake env comparator verification/round-two-point/comparator-round.json
```

- [Comparator](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097)
- [lean4export](https://github.com/leanprover/lean4export/tree/15f6055e299ad5b89345e533cc2192f4cc00f659)
- [Landrun](https://github.com/zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4)
- [Nanoda](https://github.com/ammkrn/nanoda_lib/tree/079049d584b2aed2b0172218164082f4fc6eede2)
