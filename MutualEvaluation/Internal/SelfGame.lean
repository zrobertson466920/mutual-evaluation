import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.SelfAgreement
import MutualEvaluation.Internal.Transfer

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
#  self-evaluation game

The payoff is defined on every outcome law and uses only reporter 0's self pair.
Invalid critics receive zero; validity does not restrict Core's strategy space.
The value and posterior identities below concern generated fair-binary laws.
No sampling loop or Core robustness certificate is asserted.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Self
open Probability Binary
attribute [local instance] Classical.propDecidable

variable {R : Type} [Fintype R] (f : Fin 2 → Kernel Bool R)

def game : Game Bool R where
  P := rp_Self_fair
  w := f
  S := scores
  nonempty := by simp [scores]
  u := fun c ρ => if rp_Binary_Valid c then agreement c (ρ.map Prod.fst) else 0

def reported (σ : Fin 2 → Kernel R R) : Kernel Bool R :=
  fun x => (f 0 x).bind (σ 0)

theorem self_record (σ : Fin 2 → Kernel R R) :
    (law (game f) σ).map Prod.fst = repeated (reported f σ) :=
  self_law (game f) σ

theorem payoff_valid (c : Critic R) (hc : rp_Binary_Valid c) (ρ : PMF (Outcome R)) :
    (game f).u c ρ = agreement c (ρ.map Prod.fst) := by
  simp only [game, if_pos hc]

theorem payoff_invalid (c : Critic R) (hc : ¬ rp_Binary_Valid c) (ρ : PMF (Outcome R)) :
    (game f).u c ρ = 0 := by
  simp only [game, if_neg hc]

/-- A single critic attains the information value at every reporting profile. -/
theorem literal_payoff (σ : Fin 2 → Kernel R R) :
    (game f).u (rp_Binary_annotate id) (law (game f) σ) = information (reported f σ) := by
  rw [payoff_valid f _ (MutualEvaluation.Binary.annotate_valid_impl id), self_record, agreement_information]

private theorem payoff_le_information (σ : Fin 2 → Kernel R R) (c : Critic R) :
    (game f).u c (law (game f) σ) ≤ information (reported f σ) := by
  by_cases hc : rp_Binary_Valid c
  · rw [payoff_valid f c hc, self_record]
    have h := agreement_regret (reported f σ) c hc
    have hn := _root_.MutualEvaluation.Fiber.loss_nonneg (classMap c hc)
      (reportMass (reported f σ)) (posterior (reported f σ))
      (reportMass_nonneg (reported f σ))
    unfold classPosterior at h
    linarith
  · rw [payoff_invalid f c hc]
    exact information_nonneg _

/-- The supremum is over all binary critics, including invalid critics. -/
theorem value (σ : Fin 2 → Kernel R R) :
    V (game f) (law (game f) σ) = information (reported f σ) := by
  obtain ⟨c, hc⟩ := Abstract.regret_attained (game f) (law (game f) σ)
  have hc' := (Abstract.regret_zero_iff (game f) c (law (game f) σ)).1 hc
  apply le_antisymm
  · rw [← hc']
    exact payoff_le_information f σ c
  · rw [← literal_payoff f σ]
    exact sub_nonneg.mp (Abstract.regret_nonneg (game f) _ _)

/-- This is the actual derived regret of the Game, not an assumed loss. -/
theorem regret_formula (σ : Fin 2 → Kernel R R) (c : Critic R) (hc : rp_Binary_Valid c) :
    Abstract.regret (game f) c (law (game f) σ) =
      4 * ∑ a, reportMass (reported f σ) a *
        (posterior (reported f σ) a - classPosterior c hc (reported f σ) a)^2 := by
  change V (game f) (law (game f) σ) -
    (game f).u c (law (game f) σ) = _
  rw [value f σ, payoff_valid f c hc, self_record f σ]
  exact agreement_regret (reported f σ) c hc

/-- Global validity, but posterior sufficiency only on positive-mass support. -/
theorem optimal_iff (σ : Fin 2 → Kernel R R) (c : Critic R) (hc : rp_Binary_Valid c) :
    (game f).u c (law (game f) σ) = V (game f) (law (game f) σ) ↔
      ∀ a b, rp_Binary_Rel c a b →
        0 < reportMass (reported f σ) a → 0 < reportMass (reported f σ) b →
          posterior (reported f σ) a = posterior (reported f σ) b := by
  refine (Abstract.regret_zero_iff (game f) c (law (game f) σ)).symm.trans ?_
  rw [regret_formula f σ c hc,
    mul_eq_zero, or_iff_right (by norm_num : (4 : ℝ) ≠ 0)]
  unfold classPosterior
  rw [_root_.MutualEvaluation.Fiber.loss_zero_iff _ _ _
    (reportMass_nonneg (reported f σ))]
  simp only [classMap_eq_iff]

/-- The second reporting policy is payoff-irrelevant even at a nonoptimal critic. -/
theorem peer_irrelevant (σ τ : Fin 2 → Kernel R R) (h : σ 0 = τ 0) (c : Critic R) :
    (game f).u c (law (game f) σ) = (game f).u c (law (game f) τ) := by
  have hk : reported f σ = reported f τ := by
    funext x
    change (f 0 x).bind (σ 0) = (f 0 x).bind (τ 0)
    rw [h]
  by_cases hc : rp_Binary_Valid c
  · rw [payoff_valid f c hc, payoff_valid f c hc, self_record, self_record, hk]
  · rw [payoff_invalid f c hc, payoff_invalid f c hc]

end MutualEvaluation.Self
end