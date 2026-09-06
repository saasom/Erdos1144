# Third-party notices

## Shared Erdős #520 development

The modules under `Erdos/Problem520/` are the part of the local Erdős #520
development imported by this proof. The associated public development is
<https://github.com/saasom/Erdos520>, authored by Sigurd Høystad and released
under Apache License 2.0. This repository records its exact packaged source
versions in `verification/source-snapshot.sha256`; subsequent local
extensions needed by #1144 are included in that snapshot.

## Prime number theorem

The files under `Erdos/Problem520/External/PNT/` are adapted from
`AlexKontorovich/PrimeNumberTheoremAnd`, tag `v4.29.0`, commit
`d7f9e2bfdcc7e34dfb9328b7494a6d424ff50c96`.

The files under `Erdos/Problem520/External/Architect/` are adapted from
`hanwenzhu/LeanArchitect`, tag `v4.29.0`, commit
`719ea595bb100be70d0b53b01eca828862d9f860`.

Both are distributed under Apache License 2.0. Their license texts and the
porting record are included as `ARCHITECT_LICENSE`, `PNT_LICENSE`, and
`PNT_PROVENANCE.md` in the external-source directory. Original copyright
headers are retained.

## Selberg sieve and Brun–Titchmarsh

The files under `Erdos/Problem520/External/Sieve/` and
`Erdos/Problem520/External/BrunTitchmarsh.lean` retain their original copyright
headers for Arend Mellendijk and are released under Apache License 2.0.
The Apache 2.0 license text is included in this repository.

## Lean and Mathlib

Lean, Mathlib and their package dependencies are fetched at the revisions
recorded in `lake-manifest.json`. They retain their respective upstream
licenses and copyright notices.
