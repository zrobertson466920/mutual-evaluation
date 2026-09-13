import MutualEvaluation.Public.CriticTiming

/-!
All 27 selected timing declarations are actual Lean code in Public/CriticTiming.
These checks inspect the 18 definitions/abbreviations and nine theorem proofs,
including their recursive dependencies. The public annotation has one file;
the upstream calculation modules use expanded expressions, not public imports.
-/

#print MutualEvaluation.Timing.truthLaw
#check @MutualEvaluation.Timing.truth_attained
#print MutualEvaluation.Timing.CA
#print MutualEvaluation.Timing.VPP
#check @MutualEvaluation.Timing.at_truth
#check @MutualEvaluation.Timing.timing_gap
#print MutualEvaluation.Abstract.truthValueMaximal
#check @MutualEvaluation.Abstract.truthful_global_optimal
#print MutualEvaluation.Binary.scores
#print MutualEvaluation.Binary.Critic
#print MutualEvaluation.Probability.mass
#print MutualEvaluation.Timing.CAVPP.μ
#print MutualEvaluation.Timing.CAVPP.π
#print MutualEvaluation.Timing.CAVPP.T
#print MutualEvaluation.Timing.CAVPP.J
#check @MutualEvaluation.Timing.CAVPP.variational_TV
#print MutualEvaluation.Timing.CAVPP.game
#check @MutualEvaluation.Timing.CAVPP.value
#check @MutualEvaluation.Timing.CAVPP.regret_formula
#check @MutualEvaluation.Timing.CAVPP.guarantees
#print MutualEvaluation.Timing.CAVPP.Example.prior
#print MutualEvaluation.Timing.CAVPP.Example.workers
#print MutualEvaluation.Timing.CAVPP.Example.G
#print MutualEvaluation.Timing.CAVPP.Example.agreement
#print MutualEvaluation.Timing.CAVPP.Example.flip
#print MutualEvaluation.Timing.CAVPP.Example.changed
#check @MutualEvaluation.Timing.CAVPP.Example.timing_table

#print axioms MutualEvaluation.Timing.truthLaw
#print axioms MutualEvaluation.Timing.truth_attained
#print axioms MutualEvaluation.Timing.CA
#print axioms MutualEvaluation.Timing.VPP
#print axioms MutualEvaluation.Timing.at_truth
#print axioms MutualEvaluation.Timing.timing_gap
#print axioms MutualEvaluation.Abstract.truthValueMaximal
#print axioms MutualEvaluation.Abstract.truthful_global_optimal
#print axioms MutualEvaluation.Binary.scores
#print axioms MutualEvaluation.Binary.Critic
#print axioms MutualEvaluation.Probability.mass
#print axioms MutualEvaluation.Timing.CAVPP.μ
#print axioms MutualEvaluation.Timing.CAVPP.π
#print axioms MutualEvaluation.Timing.CAVPP.T
#print axioms MutualEvaluation.Timing.CAVPP.J
#print axioms MutualEvaluation.Timing.CAVPP.variational_TV
#print axioms MutualEvaluation.Timing.CAVPP.game
#print axioms MutualEvaluation.Timing.CAVPP.value
#print axioms MutualEvaluation.Timing.CAVPP.regret_formula
#print axioms MutualEvaluation.Timing.CAVPP.guarantees
#print axioms MutualEvaluation.Timing.CAVPP.Example.prior
#print axioms MutualEvaluation.Timing.CAVPP.Example.workers
#print axioms MutualEvaluation.Timing.CAVPP.Example.G
#print axioms MutualEvaluation.Timing.CAVPP.Example.agreement
#print axioms MutualEvaluation.Timing.CAVPP.Example.flip
#print axioms MutualEvaluation.Timing.CAVPP.Example.changed
#print axioms MutualEvaluation.Timing.CAVPP.Example.timing_table
