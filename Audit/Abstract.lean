import MutualEvaluation.Public.Abstract

/-!
# Abstract results — review batch A inspection

Run with:
  lake env lean -DwarningAsError=true Audit/Abstract.lean

These are derived results in the annotated interface, not new model assumptions.
The checks expose all theorem hypotheses, including finiteness and the
normalization required by payoff realization. Foundational audits are separate
from author approval. Equal-envelope robustness and committed loss now have
their annotated home in Abstract.
-/

open MutualEvaluation
open MutualEvaluation.Abstract

/-! Two public constructions: derived regret and replacement of the payoff. -/
#print regret
#print withRegret

/-! Rows 1–2: decomposition, normalization, and converse realization. -/
#check @payoff_eq_value_sub_regret
#check @regret_nonneg
#check @regret_zero_iff
#check @regret_attained
#check @realizes_regret

/-! Row 3: distinguish all outcome laws from generated reporting laws. -/
#check @gap_iff_regret_invariant
#check @gap_iff_separable
#check @reporting_gap_iff_regret_invariant
#check @reporting_gap_iff_separable

/-! Recursive foundational dependencies of every inspected declaration in this batch. -/
#print axioms regret
#print axioms withRegret
#print axioms payoff_eq_value_sub_regret
#print axioms regret_nonneg
#print axioms regret_zero_iff
#print axioms regret_attained
#print axioms realizes_regret
#print axioms gap_iff_regret_invariant
#print axioms gap_iff_separable
#print axioms reporting_gap_iff_regret_invariant
#print axioms reporting_gap_iff_separable
/-! These signatures were already annotated; their declarations now live in Public/Abstract. -/
#check @same_value_robustness_iff
#check @committed_loss
#print axioms same_value_robustness_iff
#print axioms committed_loss
