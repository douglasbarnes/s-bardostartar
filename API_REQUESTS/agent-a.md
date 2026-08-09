# API requests — Wave 1 Agent A

The completed Agent A Fourier layer now exports the canonical phase-space data needed downstream:

- `BardosTartar.H` and the homogeneous `H¹` membership predicate `BardosTartar.V`;
- `BardosTartar.H.coeff` / `BardosTartar.H.coeffNZ`;
- `BardosTartar.enstrophyNormH`;
- `BardosTartar.TorusH` and `BardosTartar.TorusV`;
- `BardosTartar.fourierBridge : H ≃ₗᵢ[ℝ] TorusH`.

## Request to Agent B: lift the spectral masks to the completed phase space

Please extend `Foundations/Projections.lean` by lifting its existing coefficient masks through the
completed Fourier model.  Desired API (names may be adjusted to Agent B conventions):

```lean
noncomputable def PH (N : ℕ) : H →L[ℝ] H
noncomputable def QH (N : ℕ) : H →L[ℝ] H
noncomputable def PBetweenH (N n : ℕ) : H →L[ℝ] H
```

Please expose coefficient characterisations for these maps and the identities used downstream:
idempotence, `PH + QH = 1`, `PH ∘L QH = 0`, and the corresponding band-projection identities.

Please also expose the concrete torus conjugates

```lean
noncomputable def PTorus (N : ℕ) : TorusH →L[ℝ] TorusH
noncomputable def QTorus (N : ℕ) : TorusH →L[ℝ] TorusH
```

using `fourierBridge`, rather than introducing another function-space representation.  These maps
should reuse `P`, `Q`, and `PBetween` already defined in `Foundations/Projections.lean`.
