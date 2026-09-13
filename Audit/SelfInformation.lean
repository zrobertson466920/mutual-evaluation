import MutualEvaluation.Public.Replication
import MutualEvaluation.Internal.FiberVariance
import MutualEvaluation.Internal.SelfInformation

/-! Supporting algebra and binary experiment; not a replication-loop certificate. -/
open MutualEvaluation

#print Self.repeated
#print Self.reportMass
#print Self.posterior
#print Self.information
#print Self.reference
#check @Self.posterior_bayes
#check @Self.reference_dominated
#check @Self.information_eq_chiSquared
#check @Fiber.decomposition
#check @Fiber.loss_zero_iff

#print axioms Fiber.push
#print axioms Fiber.mean
#print axioms Fiber.push_mul
#print axioms Fiber.weight_le_push
#print axioms Fiber.weight_zero
#print axioms Fiber.mass_mul_mean
#print axioms Fiber.decomposition
#print axioms Fiber.loss_nonneg
#print axioms Fiber.loss_zero_iff

#print axioms Self.fair
#print axioms Self.repeated
#print axioms Self.reportMass
#print axioms Self.posterior
#print axioms Self.information
#print axioms Self.joint
#print axioms Self.reference
#print axioms Self.chiSquared
#print axioms Self.reportMass_nonneg
#print axioms Self.reportMass_sum
#print axioms Self.weighted_posterior
#print axioms Self.repeated_marginal
#print axioms Self.posterior_bayes
#print axioms Self.repeated_posterior
#print axioms Self.reference_dominated
#print axioms Self.information_eq_chiSquared
#print axioms Self.information_nonneg
#print axioms Self.information_le_one