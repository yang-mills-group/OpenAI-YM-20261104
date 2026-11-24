# Wilson Yang–Mills comparators

## What the comparators verify

For each compact matrix gauge group whose Lie algebra is simple, the existence comparator verifies the following properties of the corresponding four-dimensional Yang–Mills theory.

- At fixed volume, correlation functions of renormalised local operators on the Wilson lattice converge as the lattice spacing tends to zero when smeared away from coincident points. The operators are labelled in the ultraviolet by all gauge-invariant polynomials in the free field strength and its derivatives, subject to the free field equations and the Bianchi identity.
- Every strictly increasing sequence of the prescribed volumes has a subsequence giving an infinite-volume limit. A vacuum sector of that limit yields a theory satisfying the Wightman axioms.
- The theory has a symmetric, conserved stress tensor satisfying the translation and rotation Ward identities. Its local fields admit an asymptotic operator product expansion (OPE).
- At short distances, after a scale-dependent field renormalisation, correlation functions approach those of free Yang–Mills theory.
- The connected two-point function of the trace of the stress tensor has the short-distance behaviour predicted by the Yang–Mills trace anomaly. This distinguishes the theory from free Yang–Mills.

The matching comparator additionally verifies that the correlation functions and OPE coefficients of the resulting theory match those of an independently prescribed $\overline{\mathrm{MS}}$ scheme to all orders in perturbation theory.

Neither comparator proves that a mass gap exists or that the infinite-volume limit and its vacuum sector are unique. Both those results would require significantly more control over the infrared behaviour of the theory.

## Lean statements and proofs

| Theorem | Challenge | Solution | Verification configuration |
|---|---|---|---|
| `YangMills.jointExistence` | [Statement](lean/Comparators/Existence/Challenge.lean) | [Proof](lean/Comparators/Existence/Solution.lean) | [Existence.json](lean/ComparatorChallenges/Existence.json) |
| `YangMills.perturbativeMatching` | [Statement](lean/Comparators/Matching/Challenge.lean) | [Proof](lean/Comparators/Matching/Solution.lean) | [Matching.json](lean/ComparatorChallenges/Matching.json) |

The two proofs share a single Lake project. See the [verification instructions](NOTES.md) for the pinned tools and the commands for each theorem.

The Lean code is itself *strongly interacting in the IR* — near the end of Matching, a single compiler process loads much of the dependency tree.
Before starting Matching on Linux, check the [memory-map limit](NOTES.md#linux-memory-maps).
