import MutualEvaluation.Internal.ReplicationExpressions
import Mathlib

/-!
INTERNAL / DRAFT — finite logarithmic divergence algebra.
The real-valued sum below is used as KL divergence only when the first weight
vector is dominated by the second. Domination is explicit in the theorems;
real division and log at zero must not conceal a singular contribution.
No replication measure or expected-payment identity is used.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.FiniteLog

private theorem atom_gap_nonneg (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hd : q = 0 → p = 0) :
    0 ≤ p * Real.log (p / q) - p + q := by
  by_cases hp0 : p = 0
  · simpa [hp0] using hq
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hq0 : q ≠ 0 := fun h => hp0 (hd h)
    have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hc : p * (q / p) = q := by field_simp
    have hl := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hq' hp')) hp
    simp only [Real.log_div hq0 hp0, mul_sub, hc, mul_one] at hl
    rw [Real.log_div hp0 hq0]
    nlinarith

private theorem atom_gap_zero_iff (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hd : q = 0 → p = 0) :
    p * Real.log (p / q) - p + q = 0 ↔ p = q := by
  constructor
  · intro he
    by_cases hp0 : p = 0
    · have hq0 : q = 0 := by simpa [hp0] using he
      exact hp0.trans hq0.symm
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have hq0 : q ≠ 0 := fun h => hp0 (hd h)
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      by_contra hpq
      have hr : q / p ≠ 1 := by
        intro h
        have hqp : q = p := by
          simpa only [one_mul] using (div_eq_iff hp0).mp h
        exact hpq hqp.symm
      have hc : p * (q / p) = q := by field_simp
      have hl := mul_lt_mul_of_pos_left
        (Real.log_lt_sub_one_of_pos (div_pos hq' hp') hr) hp'
      simp only [Real.log_div hq0 hp0, mul_sub, hc, mul_one] at hl
      rw [Real.log_div hp0 hq0] at he
      nlinarith
  · intro he
    rw [he]
    simp

variable {A : Type} [Fintype A]

/- Finite logarithmic sum. Its divergence interpretation requires domination,
rather than treating a positive numerator over zero as a valid KL term. -/


theorem divergence_self (p : A → ℝ) : rp_FiniteLog_divergence p p = 0 := by
  simp []

/-- Logarithms can be split on dominated atoms, including zero-mass atoms. -/
theorem divergence_eq_sub (p q : A → ℝ) (hd : ∀ a, q a = 0 → p a = 0) :
    rp_FiniteLog_divergence p q = ∑ a, p a * (Real.log (p a) - Real.log (q a)) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p a = 0
  · simp [hp]
  · have hq : q a ≠ 0 := fun h => hp (hd a h)
    rw [Real.log_div hp hq]

private theorem divergence_eq_sum_gap (p q : A → ℝ)
    (hs : ∑ a, p a = ∑ a, q a) :
    rp_FiniteLog_divergence p q = ∑ a, (p a * Real.log (p a / q a) - p a + q a) := by
  simp only [ Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
  ring

/-- Gibbs' inequality for dominated nonnegative vectors of equal total mass.
Probability vectors are the special case where both totals equal one. -/
theorem divergence_nonneg (p q : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ a, q a = 0 → p a = 0) (hs : ∑ a, p a = ∑ a, q a) :
    0 ≤ rp_FiniteLog_divergence p q := by
  rw [divergence_eq_sum_gap p q hs]
  exact Finset.sum_nonneg (fun a _ =>
    atom_gap_nonneg (p a) (q a) (hp a) (hq a) (hd a))

/-- Equality in Gibbs' inequality identifies the entire finite weight vector. -/
theorem divergence_zero_iff (p q : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ a, q a = 0 → p a = 0) (hs : ∑ a, p a = ∑ a, q a) :
    rp_FiniteLog_divergence p q = 0 ↔ p = q := by
  rw [divergence_eq_sum_gap p q hs,
    Finset.sum_eq_zero_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) =>
      atom_gap_nonneg (p a) (q a) (hp a) (hq a) (hd a))]
  constructor
  · intro h
    funext a
    exact (atom_gap_zero_iff (p a) (q a) (hp a) (hq a) (hd a)).1
      (h a (Finset.mem_univ a))
  · intro h a _
    exact (atom_gap_zero_iff (p a) (q a) (hp a) (hq a) (hd a)).2 (congrFun h a)

end MutualEvaluation.FiniteLog
end