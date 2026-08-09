# API requests — Wave 1 Agent C

Agent C still needs concrete canonical PDE objects before the PDE-specific citation
statement interfaces can be replaced by exact citation axioms.  This request is now
narrower than the original one: Wave 1 has since supplied the canonical lattice spectrum
and coefficient-level spectral masks.

## Already available

The citation integration should reuse, not redefine:

- `BardosTartar.lambda` and its indexing convention from `Foundations/Spectrum.lean`;
- the low/high coefficient masks `BardosTartar.P` and `BardosTartar.Q` from
  `Foundations/Projections.lean`;
- the torus/Fourier conventions in `Foundations/Torus.lean` and
  `Foundations/Fourier.lean`.

## Still needed from the phase-space/Fourier bridge

Please expose the canonical project objects sufficient to identify:

- the real mean-zero divergence-free `L²` phase space `H`;
- the `H¹`/enstrophy space or predicate `V`;
- the paper norms `|u|` and `‖u‖` on those spaces;
- the Fourier coefficient equivalence/embedding connecting `H` to the repository's
  coefficient representation;
- concrete phase-space maps `P_n`, `Q_n` obtained from the existing coefficient masks.

`Foundations/Projections.lean` already notes that its concrete function-space projections
must be obtained through the missing Fourier equivalence.  Agent C must use that bridge
rather than introduce another function-space model.

## Still needed from the dynamics layer

Please expose a concrete predicate/type for a 2D periodic Navier--Stokes solution on a
time set/interval and the positive-time solution operator/semigroup used by the project.
Agent C needs signatures equivalent in role to:

```lean
-- schematic only; names/types should follow the repository's actual API
NSESolutionOn : Set ℝ → (ℝ → H) → Prop
S : ℝ → H → H
```

with enough linkage between `NSESolutionOn` and `S` to specialize the following typed
citation interfaces into individually named assumptions on canonical objects:

- `constantinFoias_temam_periodic2D_wellPosedness_statement`;
- `bardosTartar_periodic2D_backwardsUniqueness_statement`;
- `constantinFoias_bardosTartar_periodic2D_strongDissipation_statement`;
- the exact 2D-NSE instance corresponding to `cfkm_lemma3_9_theorem3_1_statement`;
- `gevrey_theorem1_1_statement` (time analyticity only).

No new analytic lemma is requested here.  In particular, the power-series coefficient
growth used later in the nonextendability proof is a project proof obligation derived
from analyticity, not part of the Gevrey citation axiom.
