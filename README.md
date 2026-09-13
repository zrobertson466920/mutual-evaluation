# Mutual evaluation

Lean 4 / Mathlib formalization, in namespace `MutualEvaluation`.
Toolchain: Lean `4.33.0`, Mathlib `v4.33.0`.

## Interface

**The Public Lean modules are the authoritative home of the declarations and
their author annotations.** Theorems include proofs checked by Lean.

| Module | Material | Declarations |
|---|---|---:|
| [Core](MutualEvaluation/Public/Core.lean) | Games, sampling, scores, robustness, and equilibrium | 19 |
| [Abstract](MutualEvaluation/Public/Abstract.lean) | Value envelopes, regret, separability, and committed loss | 13 |
| [CriticTiming](MutualEvaluation/Public/CriticTiming.lean) | CA/VPP timing, conditional transfer, Boolean objective, and example | 27 |
| [Replication](MutualEvaluation/Public/Replication.lean) | Validity, Pearson/KL replication payments, information, regret, and single-worker equilibrium | 69 |

Import all four modules with:

```lean
import MutualEvaluation
```

Internal modules supply proof dependencies and additional results. They are
included in the package, but transitive availability through an import does not
make an internal result part of the annotated interface. Public/Internal is an
annotation boundary, not Lean visibility.

## Build and check

Install [Elan](https://github.com/leanprover/elan). The checked-in toolchain and
Lake manifest pin Lean and dependencies. Audits also require Python 3.9 or later,
with no third-party Python packages.

```bash
lake exe cache get
lake build
python3 scripts/audit.py
```

The default build checks the public root and `MutualEvaluation/Internal.lean`,
with warnings treated as errors. The audit runner checks declaration ownership
and coverage against the Public sources, computational annotation closure, and
recursive dependencies against `propext`, `Classical.choice`, and `Quot.sound`.
Logs are written to `.verification/`.

Individual checks can be run after building:

```bash
python3 scripts/check_annotations.py
python3 scripts/check_interface.py
lake env lean -DwarningAsError=true Audit/Abstract.lean
```

Checks inspect source structure, formal types, and proofs; they do not establish
natural-language meaning or author intent. Changes to the public interface and
its interpretation require author review.

## Scope

Consult the Public declarations and their annotations for exact hypotheses.

Core's `robust` and `Model.robustness` concern additional garbling of **worker 0
only**, independently on that worker's replicas. `robustBoth` requires robustness
for both workers. Truthful joint optimality needs an additional value-maximality
bound; one-sided robustness alone does not imply it.

Timing assumes ideal law access. Replication covers finite task priors and finite
report alphabets without full support; sampling theorems require measurable
singletons. Both payments have termination, integrability, unbiasedness,
information envelopes, posterior regret, and truthful single-worker equilibrium
results. Invalid critics receive zero.

Replication uses one fixed reporting kernel per experiment, not within-loop
adaptive strategies. Its equilibrium is distinct from Core's two-worker Nash
predicate and is not a `Model.robustness` certificate. Pearson's expected score
has an internal same-task-pair-law factorization; no such claim is made for KL.

Sampling-cost and variance identities, learned-score guarantees, and adaptive
strategies are not implemented. No semantic correctness, unique-equilibrium,
or efficient-learning guarantee is claimed.
