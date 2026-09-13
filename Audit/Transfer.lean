import MutualEvaluation.Internal.Transfer

/-! Statement and recursive foundational inspection, separate from author review. -/
open MutualEvaluation.Abstract

#check @same_value_robustness_iff
#check @committed_loss
#check @transfer_le
#check @transfer_lt
#check @garbling_loss
#print truthValueMaximal
#check @first_reporter_best_response
#check @truth_value_maximal_of_robustness
#check @truthful_global_optimal
#check @truthful_nash_of_value_maximal
#check @exists_truthful_nash

#print axioms same_value_robustness_iff
#print axioms committed_loss
#print axioms transfer_le
#print axioms transfer_lt
#print axioms garbling_loss
#print axioms truthValueMaximal
#print axioms first_reporter_best_response
#print axioms truth_value_maximal_of_robustness
#print axioms truthful_global_optimal
#print axioms truthful_nash_of_value_maximal
#print axioms exists_truthful_nash