import MutualEvaluation.Internal.TimingInstances

/-! Two-independent-task sampling and concrete timing, not replication loops. -/
open MutualEvaluation.Timing

#print Sampling.reduce
#print Sampling.payment
#print Sampling.expected
#check @Sampling.same_transcript
#check @Sampling.expected_eq
#check @Sampling.expected_record_eq
#print Example.prior
#print Example.workers
#print Example.bonus
#print Example.mediated
#print Example.flip
#print Example.ρ
#print Example.ν
#check @Example.payoff_table
#check @Example.value_table
#check @Example.commitment_gap
#check @Example.regret_table
#check @Example.truthful_nash

#print axioms Sampling.reduce
#print axioms Sampling.payment
#print axioms Sampling.expected
#print axioms Sampling.same_transcript
#print axioms Sampling.expected_eq
#print axioms Sampling.expected_record_eq
#print axioms Example.prior
#print axioms Example.workers
#print axioms Example.bonus
#print axioms Example.mediated
#print axioms Example.flip
#print axioms Example.ρ
#print axioms Example.ν
#print axioms Example.payoff_table
#print axioms Example.value_table
#print axioms Example.commitment_gap
#print axioms Example.regret_table
#print axioms Example.truthful_nash