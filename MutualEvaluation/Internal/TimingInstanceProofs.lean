import MutualEvaluation.Internal.TimingPayoffProofs

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
# Timing instances: two-task payment and reversible reporting

The payment samples two independent cross pairs. They are not the two
same-task replicas of one Core outcome. The fair-bit example compares
law-level critic commitment and reoptimization, not samplewise critic selection.
-/

noncomputable section
namespace MutualEvaluation.Timing
open Boolean Probability Probability.Proofs Abstract

local notation "mass" => (fun {A : Type} (p : PMF A) (a : A) => ENNReal.toReal (p a))
local notation "scores" => ({0, 1} : Finset ℝ)
local notation "Critic" => (fun R : Type => R × R → ({0, 1} : Finset ℝ))

private theorem objective_formula (c : Critic Bool) (μ : PMF (Bool × Bool)) :
    J c μ = determinant μ *
      ((c (false, false) : ℝ) + (c (true, true) : ℝ) -
        (c (false, true) : ℝ) - (c (true, false) : ℝ)) := by
  unfold J
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul, Fintype.sum_prod_type, Boolean.residual]
  simp
  ring

namespace Sampling

def reduce (positive negative : scores) : ℝ :=
  1 + ((positive : ℝ) - (negative : ℝ)) / 2

def payment (c : Critic Bool) (p q : Bool × Bool) : ℝ :=
  reduce (c p) (c (p.1, q.2))

/-- The product of masses specifies two independent pair samples. -/
def expected (c : Critic Bool) (μ : PMF (Bool × Bool)) : ℝ :=
  ∑ p, ∑ q, (mass μ p * mass μ q) * payment c p q

/-- Cross-record noninterference: only the two queried scores affect payment. -/
theorem same_transcript (c d : Critic Bool) (p q p' q' : Bool × Bool)
    (hp : c p = d p') (hn : c (p.1, q.2) = d (p'.1, q'.2)) :
    payment c p q = payment d p' q' := by
  simp only [payment, hp, hn]

theorem expected_eq (c : Critic Bool) (μ : PMF (Bool × Bool)) :
    expected c μ = 1 + J c μ / 2 := by
  have ht := mass_sum μ
  have h00 : mass μ (false, false) =
      1 - mass μ (false, true) - mass μ (true, false) - mass μ (true, true) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool] at ht
    linarith
  rw [objective_formula]
  simp only [expected, payment, reduce, determinant,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [h00]
  ring

/-- A two-independent-task realization of the primitive record-law payoff. -/
theorem expected_record_eq {X : Type} (P : PMF X)
    (f : Fin 2 → Kernel X Bool) (c : Critic Bool) (ρ : PMF (Outcome Bool)) :
    expected c (cross ρ) = (mediatedGame P f).u c ρ :=
  expected_eq c (cross ρ)

end Sampling

namespace Example

def prior : PMF Bool := PMF.uniformOfFintype Bool
def workers : Fin 2 → Kernel Bool Bool := fun _ => PMF.pure
abbrev bonus : Game Bool Bool := bonusGame prior workers
abbrev mediated : Game Bool Bool := mediatedGame prior workers
def flip : Kernel Bool Bool := fun b => PMF.pure (!b)
def ρ : PMF (Outcome Bool) := law bonus truth
def ν : PMF (Outcome Bool) := law bonus (Function.update truth 0 flip)

private theorem cross_truth :
    cross ρ = prior.bind (fun x => PMF.pure (x, x)) := by
  rw [ρ, cross_law]
  change (prior.bind fun x =>
    pair ((PMF.pure x).bind PMF.pure) ((PMF.pure x).bind PMF.pure)) = _
  simp only [PMF.pure_bind, pair, PMF.pure_map]

private theorem cross_flip :
    cross ν = prior.bind (fun x => PMF.pure (!x, x)) := by
  rw [ν, cross_law]
  change (prior.bind fun x =>
    pair ((PMF.pure x).bind (Function.update truth 0 flip 0))
      ((PMF.pure x).bind (Function.update truth 0 flip 1))) = _
  simp [truth, flip, pair, PMF.pure_bind, PMF.pure_map]

private theorem mass_truth (a b : Bool) :
    mass (cross ρ) (a, b) = if a = b then (1 / 2 : ℝ) else 0 := by
  rw [cross_truth, mass_bind]
  cases a <;> cases b <;>
    norm_num [prior, PMF.uniformOfFintype_apply, PMF.pure_apply]

private theorem mass_flip (a b : Bool) :
    mass (cross ν) (a, b) = if a = b then 0 else (1 / 2 : ℝ) := by
  rw [cross_flip, mass_bind]
  cases a <;> cases b <;>
    norm_num [prior, PMF.uniformOfFintype_apply, PMF.pure_apply]

private theorem statistics :
    TV (cross ρ) = 1 / 2 ∧ TV (cross ν) = 1 / 2 ∧
      J agree (cross ρ) = 1 / 2 ∧ J agree (cross ν) = -(1 / 2) := by
  norm_num [TV_eq, D, determinant, mass_truth, mass_flip,
    objective_formula, agree]

theorem payoff_table :
    bonus.u agree ρ = 5 / 4 ∧ bonus.u agree ν = 5 / 4 ∧
      mediated.u agree ρ = 5 / 4 ∧ mediated.u agree ν = 3 / 4 := by
  change
    TV (cross ρ) / 2 + (agree (false, false) : ℝ) = 5 / 4 ∧
    TV (cross ν) / 2 + (agree (false, false) : ℝ) = 5 / 4 ∧
    1 + J agree (cross ρ) / 2 = 5 / 4 ∧ 1 + J agree (cross ν) / 2 = 3 / 4
  rw [statistics.1, statistics.2.1, statistics.2.2.1, statistics.2.2.2]
  norm_num [agree]

theorem value_table :
    V bonus ρ = 5 / 4 ∧ V bonus ν = 5 / 4 ∧
      V mediated ρ = 5 / 4 ∧ V mediated ν = 5 / 4 := by
  rw [(values prior workers ρ).1, (values prior workers ν).1,
    (values prior workers ρ).2, (values prior workers ν).2]
  norm_num [statistics.1, statistics.2.1]

/-- Value-preserving reversible reporting can still lower committed payoff. -/
theorem commitment_gap :
    (V bonus ν = V bonus ρ ∧ V mediated ν = V mediated ρ) ∧
      bonus.u agree ν = bonus.u agree ρ ∧ mediated.u agree ν < mediated.u agree ρ := by
  rcases value_table with ⟨h₁, h₂, h₃, h₄⟩
  rcases payoff_table with ⟨h₅, h₆, h₇, h₈⟩
  norm_num [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]

theorem regret_table :
    regret bonus agree ρ = 0 ∧ regret bonus agree ν = 0 ∧
      regret mediated agree ρ = 0 ∧ regret mediated agree ν = 1 / 2 := by
  rcases value_table with ⟨h₁, h₂, h₃, h₄⟩
  rcases payoff_table with ⟨h₅, h₆, h₇, h₈⟩
  norm_num [regret, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]



end Example
end MutualEvaluation.Timing
end