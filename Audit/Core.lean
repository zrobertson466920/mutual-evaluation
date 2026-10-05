import MutualEvaluation.Public.Core

/-! Technical inspection of the annotated Core. This file is not an annotation. -/
open MutualEvaluation

#print Kernel
#print pair
#print Score
#print Score.envelope
#print independent

#print axioms Kernel
#print axioms pair
#print axioms Score
#print axioms Score.envelope
#print axioms independent

/-! Shared-only clients need no assumptions on the outcome type. -/
noncomputable section
variable {R Outcome : Type}

example (U : Score R (PMF Outcome)) (ρ : PMF Outcome) : ℝ :=
  U.envelope ρ

example (U : Score R (PMF (List R))) (ρ : PMF (List R)) : ℝ :=
  U.envelope ρ

example : Score R (PMF (List R)) :=
  ⟨{0}, by simp, fun _ _ => 0⟩

end