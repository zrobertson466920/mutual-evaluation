import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationRecurrence

/-!
INTERNAL — measurability and termination for the draft replication experiment.
Validity supplies reflexivity; positive-mass anchors supply positive target
probabilities. No full-support hypothesis and no assumed waiting-time law.
Integrability and unbiasedness are separate obligations.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open MeasureTheory Binary
open Internal.ReplicationPaths

variable {X R : Type} [MeasurableSpace R] [Fintype R]
  [MeasurableSingletonClass R]

private theorem measurable_comparison {Ω : Type*} [MeasurableSpace Ω]
    (c : Critic R) (f g : Ω → R) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {ω | rp_Binary_Rel c (f ω) (g ω)} :=
  (Set.toFinite {ab : R × R | rp_Binary_Rel c ab.1 ab.2}).measurableSet.preimage
    (hf.prodMk hg)

theorem measurable_R_specific (c : Critic R) : Measurable (rp_Replication_R_specific c) := by
  apply measurable_firstHit
  intro n
  exact measurable_comparison c _ _ measurable_fst
    ((measurable_pi_apply n).comp (measurable_fst.comp measurable_snd))

theorem measurable_R_null (c : Critic R) : Measurable (rp_Replication_R_null c) := by
  apply measurable_firstHit
  intro n
  exact measurable_comparison c _ _ measurable_fst
    ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd))

private theorem measurable_termination (c : Critic R) :
    MeasurableSet {t : rp_Replication_Transcript R |
      rp_Replication_R_specific c t ≠ ⊤ ∧ rp_Replication_R_null c t ≠ ⊤} :=
  ((measurableSet_singleton (⊤ : ℕ∞)).preimage (measurable_R_specific c)).compl.inter
    ((measurableSet_singleton (⊤ : ℕ∞)).preimage (measurable_R_null c)).compl

theorem ae_mass_pos (p : PMF R) : ∀ᵐ a ∂p.toMeasure, 0 < p a := by
  classical
  apply ae_iff.mpr
  rw [p.toMeasure_apply_fintype]
  apply Finset.sum_eq_zero
  intro a _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs with ha
  · rfl
  · exact le_antisymm (le_of_not_gt ha) zero_le

omit [Fintype R] in
theorem target_pos (c : Critic R) (hc : rp_Binary_Valid c)
    (p : PMF R) (a : R) (ha : 0 < p a) :
    0 < p.toMeasure {b | rp_Binary_Rel c a b} := by
  calc
    0 < p a := ha
    _ = p.toMeasure {a} :=
      (p.toMeasure_apply_singleton a (measurableSet_singleton a)).symm
    _ ≤ p.toMeasure {b | rp_Binary_Rel c a b} :=
      measure_mono (Set.singleton_subset_iff.mpr (hc.refl a))

private theorem conditional_termination (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) (x : X) (hx : 0 < P x) :
    ∀ᵐ t ∂rp_Replication_conditionalTranscriptLaw P k x,
      rp_Replication_R_specific c t ≠ ⊤ ∧ rp_Replication_R_null c t ≠ ⊤ := by
  dsimp only
  apply (Measure.ae_prod_iff_ae_ae (measurable_termination c)).mpr
  filter_upwards [ae_mass_pos (k x)] with a ha
  have ha' : a ∈ (P.bind k).support := by
    rw [PMF.mem_support_bind_iff]
    exact ⟨x, ne_of_gt hx, ne_of_gt ha⟩
  have hE : MeasurableSet {b | rp_Binary_Rel c a b} :=
    (Set.toFinite _).measurableSet
  have hs := iid_first_hit_finite (k x) _ hE (target_pos c hc (k x) a ha)
  have hn := iid_first_hit_finite (P.bind k) _ hE
    (target_pos c hc (P.bind k) a (pos_iff_ne_zero.mpr ha'))
  apply (Measure.ae_prod_iff_ae_ae
    ((measurable_termination c).preimage (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [hs] with s hs
  filter_upwards [hn] with t ht
  exact ⟨hs, ht⟩

/-- Both potential searches terminate almost surely for a globally valid critic.
Consequently every search invoked by either payment terminates. Null task and
report atoms are discarded by the sampling law, not excluded by an assumption. -/
theorem termination_impl [Fintype X] (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) :
    ∀ᵐ t ∂rp_Replication_transcriptLaw P k, rp_Replication_R_specific c t ≠ ⊤ ∧ rp_Replication_R_null c t ≠ ⊤ := by
  apply ae_iff.mpr
  simp only [ Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : P x = 0
  · rw [hx, zero_mul]
  · have ht := ae_iff.mp (conditional_termination c hc P k x (pos_iff_ne_zero.mpr hx))
    rw [ht, mul_zero]

/-- Measurability includes the invalid-critic and nontermination branches.
It does not establish integrability. -/
theorem measurable_W_chiSquared (c : Critic R) :
    Measurable (rp_Replication_W_chiSquared c) := by
  classical
  dsimp only
  by_cases hc : rp_Binary_Valid c
  · simp only [if_pos hc]
    apply Measurable.ite
      (measurable_comparison c _ _ measurable_fst
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)))
    · exact Measurable.ite
        ((measurableSet_singleton (⊤ : ℕ∞)).preimage (measurable_R_null c))
        measurable_const
        ((measurable_of_countable (fun n : ℕ∞ => (n.toNat : ℝ) - 1)).comp
          (measurable_R_null c))
    · exact measurable_const
  · simpa only [if_neg hc] using
      (measurable_const : Measurable (fun _ : rp_Replication_Transcript R => (0 : ℝ)))

theorem measurable_W_KL (c : Critic R) :
    Measurable (rp_Replication_W_KL c) := by
  classical
  dsimp only
  by_cases hc : rp_Binary_Valid c
  · simp only [if_pos hc]
    apply Measurable.ite
      (((measurableSet_singleton (⊤ : ℕ∞)).preimage (measurable_R_null c)).union
        ((measurableSet_singleton (⊤ : ℕ∞)).preimage (measurable_R_specific c)))
      measurable_const
    exact
      ((measurable_of_countable (fun n : ℕ∞ => rp_Replication_H (n.toNat - 1))).comp
        (measurable_R_null c)).sub
      ((measurable_of_countable (fun n : ℕ∞ => rp_Replication_H (n.toNat - 1))).comp
        (measurable_R_specific c))
  · simpa only [if_neg hc] using
      (measurable_const : Measurable (fun _ : rp_Replication_Transcript R => (0 : ℝ)))

end MutualEvaluation.Replication
end