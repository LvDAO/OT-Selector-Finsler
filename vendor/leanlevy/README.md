# LeanLevy (vendored Poisson random measure sources)

Source: https://github.com/slink/LeanLevy
Commit: 7e73fd9b23ad52956ec2756a815889a783131ce4 (2026-07-15)
License: MIT (see LICENSE in this directory).

Only the files needed for the spatial Poisson random measure are vendored:

- `LeanLevy/Probability/Characteristic.lean`
- `LeanLevy/Fourier/MeasureFourier.lean`
- `LeanLevy/Probability/Poisson.lean`
- `LeanLevy/RandomMeasure/PoissonPointFamily.lean`
- `LeanLevy/RandomMeasure/PoissonRandomMeasure.lean`

The upstream toolchain is Lean v4.32.0 and mathlib rev
`1f165a51dee3b8cf9dbd45716c0b7fe05fa6bf00`; this repository pins
Lean v4.34.0-rc1.  Any local adaptations required by the newer toolchain
are confined to these files.
