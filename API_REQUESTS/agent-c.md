# API requests — Wave 1 Agent C

Agent C needs the following concrete repository objects before the PDE-specific citation statement interfaces can be specialized into exact citation axioms.  No parallel Fourier/function-space representation should be introduced to satisfy these requests.

## From the torus/Fourier foundation

Please expose the canonical project types/definitions sufficient to identify:

- the real mean-zero divergence-free `L²` phase space `H`;
- the `H¹`/enstrophy space or predicate `V`;
- the paper norms `|u|` and `‖u‖`;
- spectral projections `P_n`, `Q_n`;
- the increasing distinct Stokes eigenvalues `λ_n` and the indexing convention.

These are needed to replace the adapter fields in `Citations/Interfaces.lean` without creating a second model.

## From the dynamics layer

Please expose a concrete predicate/type for a 2D periodic Navier--Stokes solution on a time set/interval, and the positive-time solution operator/semigroup used by the project.  Agent C needs signatures equivalent in role to:

```lean
-- schematic only; names/types should follow the repository's actual API
NSESolutionOn : Set ℝ → (ℝ → H) → Prop
S : ℝ → H → H
```

with enough linkage between `NSESolutionOn` and `S` to specialize:

- `constantinFoias_temam_periodic2D_wellPosedness_statement`;
- `bardosTartar_periodic2D_backwardsUniqueness_statement`;
- `constantinFoias_bardosTartar_periodic2D_strongDissipation_statement`;
- `cfkm_lemma3_9_theorem3_1_statement`;
- `gevrey_theorem1_1_statement`.

No new analytic lemma is requested here; this is an interface request so the cited theorems can be stated on the project's canonical objects rather than on arbitrary adapter predicates.
