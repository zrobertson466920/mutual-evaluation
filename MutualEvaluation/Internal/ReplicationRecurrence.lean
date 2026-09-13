import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationLaw

/-!
INTERNAL — first-hit probabilities derived from independent call streams.
Not an additional author-certified interface. These lemmas use the pathwise
firstHit definition; no geometric count is substituted for the experiment.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open MeasureTheory
open Internal.ReplicationPaths

variable {R : Type} [MeasurableSpace R]

/-- The first n calls all miss the target event. -/
theorem iid_no_hit_prefix (p : PMF R) (E : Set R) (hE : MeasurableSet E) (n : ℕ) :
    rp_Replication_iid p {ω | ∀ m < n, ω m ∉ E} = (p.toMeasure Eᶜ)^n := by
  classical
  have he : {ω : ℕ → R | ∀ m < n, ω m ∉ E} =
      Set.pi (↑(Finset.range n) : Set ℕ) (fun _ => Eᶜ) := by
    ext ω
    simp [Set.mem_pi]
  rw [he, iid_prefix p _ _ (fun _ _ => hE.compl)]
  simp

/-- The actual first successful call is n+1: n failures followed by a success.
The success probability may be zero; no positivity assumption is hidden here. -/
theorem iid_first_hit (p : PMF R) (E : Set R) (hE : MeasurableSet E) (n : ℕ) :
    rp_Replication_iid p {ω | rp_Replication_firstHit (fun m => ω m ∈ E) = ((n + 1 : ℕ) : ℕ∞)} =
      p.toMeasure E * (p.toMeasure Eᶜ)^n := by
  classical
  have he :
      {ω : ℕ → R | rp_Replication_firstHit (fun m => ω m ∈ E) = ((n + 1 : ℕ) : ℕ∞)} =
        Set.pi (↑(insert n (Finset.range n)) : Set ℕ)
          (fun i => if i = n then E else Eᶜ) := by
    ext ω
    rw [Set.mem_ofPred_eq, firstHit_eq_succ_iff]
    change (ω n ∈ E ∧ ∀ m < n, ω m ∉ E) ↔
      ∀ i ∈ insert n (Finset.range n), ω i ∈ (if i = n then E else Eᶜ)
    constructor
    · rintro ⟨hs, hf⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using hs
      · have hi' := Finset.mem_range.mp hi
        simpa [Nat.ne_of_lt hi'] using hf i hi'
    · intro h
      refine ⟨?_, ?_⟩
      · simpa using h n (Finset.mem_insert_self _ _)
      · intro i hi
        simpa [Nat.ne_of_lt hi] using
          h i (Finset.mem_insert_of_mem (Finset.mem_range.mpr hi))
  rw [he, iid_prefix p _ _ (fun i _ => by
    split_ifs
    · exact hE
    · exact hE.compl)]
  rw [Finset.prod_insert (by simp), if_pos (rfl : n = n)]
  apply congrArg (fun z => p.toMeasure E * z)
  calc
    (∏ i ∈ Finset.range n, p.toMeasure (if i = n then E else Eᶜ)) =
        ∏ _i ∈ Finset.range n, p.toMeasure Eᶜ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hi))]
    _ = _ := by simp

/-- Nontermination is contained in every finite failure-prefix event. -/
theorem iid_nontermination_zero (p : PMF R) (E : Set R)
    (hE : MeasurableSet E) (hp : 0 < p.toMeasure E) :
    rp_Replication_iid p {ω | rp_Replication_firstHit (fun n => ω n ∈ E) = ⊤} = 0 := by
  have hr : p.toMeasure Eᶜ < 1 := by
    rw [measure_compl hE (measure_ne_top _ _), measure_univ]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ne_of_gt hp)
  have hb (n : ℕ) :
      rp_Replication_iid p {ω | rp_Replication_firstHit (fun m => ω m ∈ E) = ⊤} ≤ (p.toMeasure Eᶜ)^n := by
    rw [← iid_no_hit_prefix p E hE n]
    apply measure_mono
    intro ω hω m _
    exact (firstHit_eq_top_iff _).1 hω m
  exact le_antisymm
    (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) hb)
    zero_le

/-- Almost-sure termination derived from the actual stream, not a count oracle. -/
theorem iid_first_hit_finite (p : PMF R) (E : Set R)
    (hE : MeasurableSet E) (hp : 0 < p.toMeasure E) :
    ∀ᵐ ω ∂rp_Replication_iid p, rp_Replication_firstHit (fun n => ω n ∈ E) ≠ ⊤ := by
  apply ae_iff.mpr
  simpa only [not_not] using iid_nontermination_zero p E hE hp

end MutualEvaluation.Replication
end