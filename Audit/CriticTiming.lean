import MutualEvaluation.Internal.CriticTiming

/-!
Truthful-law commitment and actual-law reoptimization of one shared objective.
CA/VPP name the stated timing convention, not imported literature guarantees.
-/
open MutualEvaluation.Timing

#print truthLaw
#check @truth_attained
#print CA
#print VPP
#check @at_truth
#check @timing_gap
#check @reoptimized_attained
#check @timing_loss

#print CAVPP.μ
#print CAVPP.π
#print CAVPP.T
#print CAVPP.J
#check @CAVPP.variational_TV
#print CAVPP.game
#check @CAVPP.value
#check @CAVPP.regret_formula
#check @CAVPP.guarantees

#print CAVPP.Example.prior
#print CAVPP.Example.workers
#print CAVPP.Example.G
#print CAVPP.Example.agreement
#print CAVPP.Example.flip
#print CAVPP.Example.changed
#check @CAVPP.Example.timing_table
#check @CAVPP.Example.agreement_optimal
#check @CAVPP.Example.truthful_nash

#print axioms truthLaw
#print axioms truth_attained
#print axioms CA
#print axioms VPP
#print axioms at_truth
#print axioms timing_gap
#print axioms reoptimized_attained
#print axioms timing_loss
#print axioms CAVPP.μ
#print axioms CAVPP.π
#print axioms CAVPP.T
#print axioms CAVPP.J
#print axioms CAVPP.variational_TV
#print axioms CAVPP.game
#print axioms CAVPP.value
#print axioms CAVPP.regret_formula
#print axioms CAVPP.guarantees
#print axioms CAVPP.Example.prior
#print axioms CAVPP.Example.workers
#print axioms CAVPP.Example.G
#print axioms CAVPP.Example.agreement
#print axioms CAVPP.Example.flip
#print axioms CAVPP.Example.changed
#print axioms CAVPP.Example.timing_table
#print axioms CAVPP.Example.agreement_optimal
#print axioms CAVPP.Example.truthful_nash