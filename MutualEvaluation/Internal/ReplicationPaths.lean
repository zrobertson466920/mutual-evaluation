import MutualEvaluation.Internal.ReplicationExpressions
import Mathlib

/-!
INTERNAL — generic first-hit support for the draft replication interface.
These clocks are functions of actual call sequences, not geometric-law oracles.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication

attribute [local instance] Classical.propDecidable

/- Streams are zero-indexed; the returned number of calls is one-indexed.
The definition is included explicitly in the pending replication review. -/


end MutualEvaluation.Replication

namespace MutualEvaluation.Internal.ReplicationPaths
open MutualEvaluation.Replication
attribute [local instance] Classical.propDecidable

theorem firstHit_eq_top_iff (p : ℕ → Prop) :
    rp_Replication_firstHit p = ⊤ ↔ ∀ n, ¬ p n := by
  constructor
  · intro he n hn
    have h : ∃ n, p n := ⟨n, hn⟩
    simp [ h] at he
  · intro h
    have hn : ¬ ∃ n, p n := by simpa only [not_exists] using h
    simp [ hn]

theorem firstHit_eq_succ_iff (p : ℕ → Prop) (n : ℕ) :
    rp_Replication_firstHit p = ((n + 1 : ℕ) : ℕ∞) ↔
      p n ∧ ∀ m < n, ¬ p m := by
  by_cases h : ∃ n, p n
  · have he : rp_Replication_firstHit p = ((n + 1 : ℕ) : ℕ∞) ↔ Nat.find h = n := by
      simp [ h]
    rw [he, Nat.find_eq_iff]
  · have hn : ¬ p n := fun hn => h ⟨n, hn⟩
    simp only [ dif_neg h]
    constructor
    · intro he
      have hf : ((n + 1 : ℕ) : ℕ∞) ≠ ⊤ := by
        exact ENat.natCast_ne_top _
      exact (hf he.symm).elim
    · rintro ⟨hp, _⟩
      exact (hn hp).elim

theorem firstHit_congr {p q : ℕ → Prop} (h : ∀ n, p n ↔ q n) :
    rp_Replication_firstHit p = rp_Replication_firstHit q := by
  have he : p = q := funext fun n => propext (h n)
  rw [he]

theorem firstHit_ne_zero (p : ℕ → Prop) : rp_Replication_firstHit p ≠ 0 := by
  dsimp only
  split_ifs <;> simp

/-- Measurability follows from the actual finite success/failure events. -/
theorem measurable_firstHit {Ω : Type*} [MeasurableSpace Ω]
    (p : Ω → ℕ → Prop) (hp : ∀ n, MeasurableSet {ω | p ω n}) :
    Measurable (fun ω => rp_Replication_firstHit (p ω)) := by
  apply ENat.measurable_iff.mpr
  intro n
  cases n with
  | zero =>
      have he : (fun ω => rp_Replication_firstHit (p ω)) ⁻¹' {(0 : ℕ∞)} = ∅ := by
        ext ω
        exact iff_false_intro (firstHit_ne_zero (p ω))
      simp only [Nat.cast_zero]
      rw [he]
      exact MeasurableSet.empty
  | succ n =>
      have he : (fun ω => rp_Replication_firstHit (p ω)) ⁻¹' {((n + 1 : ℕ) : ℕ∞)} =
          {ω | p ω n} ∩ ⋂ m, ⋂ (_ : m < n), {ω | p ω m}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, firstHit_eq_succ_iff,
          Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq]
      rw [he]
      exact (hp n).inter (MeasurableSet.iInter fun m =>
        MeasurableSet.iInter fun _ => (hp m).compl)

end MutualEvaluation.Internal.ReplicationPaths
end