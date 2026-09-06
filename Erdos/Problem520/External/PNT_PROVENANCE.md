# Vendored prime-number-theorem proof provenance

The files under `PNT/` are the minimal import closure of the theorem
`MediumPNT` from:

- repository: `https://github.com/AlexKontorovich/PrimeNumberTheoremAnd`
- tag: `v4.29.0`
- commit: `d7f9e2bfdcc7e34dfb9328b7494a6d424ff50c96`
- license: Apache-2.0, reproduced in `PNT_LICENSE`

Only module import paths were changed to place the proof below
`Erdos.Problem520.External.PNT`.  The following compatibility changes were
needed for the project's Lean 4.30 / Mathlib 4.30 toolchain:

- two complex-coordinate simplification lists in
  `ResidueCalcOnRectangles.lean`;
- two tactic/API updates in `ZetaBounds.lean`;
- explicit complex-coordinate normalization in `MediumPNT.lean`.

The files under `Architect/` provide the blueprint commands used by those
sources and come from:

- repository: `https://github.com/hanwenzhu/LeanArchitect`
- tag: `v4.29.0`
- commit: `719ea595bb100be70d0b53b01eca828862d9f860`
- license: Apache-2.0, reproduced in `ARCHITECT_LICENSE`

Their import paths were changed to
`Erdos.Problem520.External.Architect`; `Architect/Command.lean` also contains
the small Lean 4.30 `exportEntriesFnEx?` callback-shape port.

The vendored `MediumPNT` theorem and the downstream Problem 520 oscillatory
prime-block endpoint have both been audited with `#print axioms`; they use
only `propext`, `Classical.choice`, and `Quot.sound`.
