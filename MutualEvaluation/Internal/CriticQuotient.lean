import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Public.CriticTiming

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
# Binary critics and finite annotations

Validity is global on the whole return alphabet. It is a predicate on critics,
not a restriction of Game's strategy space. No sampling or payoff is defined here.
This interface is shared by the timing and self-evaluation constructions.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Binary
attribute [local instance] Classical.propDecidable






theorem annotate_rel {R B : Type} (g : R → B) (a b : R) :
    rp_Binary_Rel (rp_Binary_annotate g) a b ↔ g a = g b := by
  by_cases h : g a = g b <;> simp [ h]

theorem annotate_valid_impl {R B : Type} (g : R → B) : rp_Binary_Valid (rp_Binary_annotate g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (annotate_rel g a a).2 rfl
  · intro a b h
    exact (annotate_rel g b a).2 ((annotate_rel g a b).1 h).symm
  · intro a b d hab hbd
    exact (annotate_rel g a d).2
      (((annotate_rel g a b).1 hab).trans ((annotate_rel g b d).1 hbd))

abbrev Classes {R : Type} (c : Critic R) (hc : rp_Binary_Valid c) :=
  Quotient (⟨rp_Binary_Rel c, hc⟩ : Setoid R)

def classMap {R : Type} (c : Critic R) (hc : rp_Binary_Valid c) : R → Classes c hc :=
  Quotient.mk _

instance classesFintype {R : Type} [Fintype R] (c : Critic R) (hc : rp_Binary_Valid c) :
    Fintype (Classes c hc) := Fintype.ofFinite _

theorem classMap_eq_iff {R : Type} (c : Critic R) (hc : rp_Binary_Valid c) (a b : R) :
    classMap c hc a = classMap c hc b ↔ rp_Binary_Rel c a b := Quotient.eq

/-! Proof helper: a binary table is determined by its score-one relation. -/
private theorem critic_ext {R : Type} (c d : Critic R)
    (h : ∀ a b, rp_Binary_Rel c a b ↔ rp_Binary_Rel d a b) : c = d := by
  funext ab
  apply Subtype.ext
  have hc : (c ab : ℝ) = 0 ∨ (c ab : ℝ) = 1 := by
    simpa [scores] using (c ab).property
  have hd : (d ab : ℝ) = 0 ∨ (d ab : ℝ) = 1 := by
    simpa [scores] using (d ab).property
  have he := h ab.1 ab.2
  rcases hc with hc | hc <;> rcases hd with hd | hd <;> simp_all []

/-- Full table equality, not just equality on observed or positive-mass reports.
The representing alphabet has at most as many elements as the return alphabet. -/
theorem valid_iff_annotation_impl {R : Type} [Fintype R] (c : Critic R) :
    rp_Binary_Valid c ↔ ∃ n ≤ Fintype.card R, ∃ g : R → Fin n, c = rp_Binary_annotate g := by
  constructor
  · intro hc
    let e := Fintype.equivFin (Classes c hc)
    refine ⟨Fintype.card (Classes c hc), ?_, e ∘ classMap c hc, ?_⟩
    · apply Fintype.card_le_of_surjective (classMap c hc)
      intro z
      refine Quotient.inductionOn z ?_
      intro a
      exact ⟨a, rfl⟩
    · apply critic_ext
      intro a b
      rw [annotate_rel]
      change rp_Binary_Rel c a b ↔ e (classMap c hc a) = e (classMap c hc b)
      constructor
      · intro h
        exact congrArg e ((classMap_eq_iff c hc a b).2 h)
      · intro h
        exact (classMap_eq_iff c hc a b).1 (e.injective h)
  · rintro ⟨n, _, g, rfl⟩
    exact MutualEvaluation.Binary.annotate_valid_impl g

end MutualEvaluation.Binary
end