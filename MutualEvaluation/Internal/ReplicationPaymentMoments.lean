import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationIntegration

/-!
INTERNAL — moments of the actual anchored-task payments.

The two-stream calculations use the existing pathwise payments and the first-hit
moments derived from independent call events. Supported anchors have positive
class probabilities; null anchors and tasks disappear under the finite mixture.
Invalid critics have constant-zero payments and are integrable as well.

The resulting class-probability sums still need to be identified with the
finite-information targets. No payment or sampling-law definition is replaced.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open MeasureTheory Binary Probability
open Internal.ReplicationPaths
attribute [local instance] Classical.propDecidable

variable {R : Type} [MeasurableSpace R] [Fintype R]
  [MeasurableSingletonClass R]

theorem streams_null_finite (c : Critic R) (p q : PMF R) (a : R)
    (hq : 0 < q.toMeasure {b | rp_Binary_Rel c a b}) :
    ∀ᵐ st ∂(rp_Replication_iid p).prod (rp_Replication_iid q), rp_Replication_R_null c (a, st) ≠ ⊤ := by
  have hm : Measurable (fun st : (ℕ → R) × (ℕ → R) => rp_Replication_R_null c (a, st)) :=
    (measurable_R_null c).comp (measurable_const.prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_singleton (⊤ : ℕ∞)).preimage hm).compl).2
  filter_upwards [] with s
  exact iid_first_hit_finite q _ (Set.toFinite _).measurableSet hq

theorem streams_specific_finite (c : Critic R) (p q : PMF R) (a : R)
    (hp : 0 < p.toMeasure {b | rp_Binary_Rel c a b}) :
    ∀ᵐ st ∂(rp_Replication_iid p).prod (rp_Replication_iid q), rp_Replication_R_specific c (a, st) ≠ ⊤ := by
  have hm : Measurable (fun st : (ℕ → R) × (ℕ → R) => rp_Replication_R_specific c (a, st)) :=
    (measurable_R_specific c).comp (measurable_const.prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_singleton (⊤ : ℕ∞)).preimage hm).compl).2
  filter_upwards [iid_first_hit_finite p _ (Set.toFinite _).measurableSet hp] with s hs
  filter_upwards [] with t
  exact hs

/-- The collision gate and null waiting time are independent at a fixed anchor.
Only the null success probability must be positive for this calculation. -/
theorem pearson_streams_moment (c : Critic R) (hc : rp_Binary_Valid c)
    (p q : PMF R) (a : R)
    (hq : 0 < q.toMeasure {b | rp_Binary_Rel c a b}) :
    Integrable (fun st => rp_Replication_W_chiSquared c (a, st)) ((rp_Replication_iid p).prod (rp_Replication_iid q)) ∧
      (∫ st, rp_Replication_W_chiSquared c (a, st) ∂(rp_Replication_iid p).prod (rp_Replication_iid q)) =
        (p.toMeasure {b | rp_Binary_Rel c a b}).toReal *
          (q.toMeasure {b | rp_Binary_Rel c a b}).toReal⁻¹ - 1 := by
  let E : Set R := {b | rp_Binary_Rel c a b}
  have hE : MeasurableSet E := (Set.toFinite E).measurableSet
  have hg : Integrable
      (fun st : (ℕ → R) × (ℕ → R) =>
        (if st.1 0 ∈ E then (1 : ℝ) else 0) *
          ((rp_Replication_firstHit (fun n => st.2 n ∈ E)).toNat : ℝ))
      ((rp_Replication_iid p).prod (rp_Replication_iid q)) := by
    simpa only [smul_eq_mul] using
      (iid_gate_integrable p E hE).smul_prod (iid_firstHit_integrable q E hE hq)
  have hae :
      (fun st => rp_Replication_W_chiSquared c (a, st)) =ᵐ[(rp_Replication_iid p).prod (rp_Replication_iid q)]
        (fun st => (if st.1 0 ∈ E then (1 : ℝ) else 0) *
          ((rp_Replication_firstHit (fun n => st.2 n ∈ E)).toNat : ℝ) - 1) := by
    filter_upwards [streams_null_finite c p q a hq] with st hn
    change rp_Replication_W_chiSquared c (a, st) =
      (if rp_Binary_Rel c a (st.1 0) then (1 : ℝ) else 0) *
        ((rp_Replication_R_null c (a, st)).toNat : ℝ) - 1
    by_cases h : rp_Binary_Rel c a (st.1 0)
    · simp only [if_pos hc, if_pos h, if_neg hn, one_mul]
    · simp only [if_pos hc, if_neg h, zero_mul, zero_sub]
  refine ⟨(hg.sub (integrable_const 1)).congr hae.symm, ?_⟩
  calc
    _ = ∫ st : (ℕ → R) × (ℕ → R),
        (if st.1 0 ∈ E then (1 : ℝ) else 0) *
          ((rp_Replication_firstHit (fun n => st.2 n ∈ E)).toNat : ℝ) - 1
          ∂(rp_Replication_iid p).prod (rp_Replication_iid q) := integral_congr_ae hae
    _ = _ := by
      rw [integral_sub hg (integrable_const 1),
        integral_prod_mul (μ := rp_Replication_iid p) (ν := rp_Replication_iid q)
          (fun s : ℕ → R => if s 0 ∈ E then (1 : ℝ) else 0)
          (fun t : ℕ → R => ((rp_Replication_firstHit (fun n => t n ∈ E)).toNat : ℝ)),
        iid_gate_integral p E hE, iid_firstHit_integral q E hE hq]
      simp [E]

/-- Both harmonic coordinates are integrable before their integrals are
subtracted. The nontermination branch differs only on a null set. -/
theorem kl_streams_moment (c : Critic R) (hc : rp_Binary_Valid c)
    (p q : PMF R) (a : R)
    (hp : 0 < p.toMeasure {b | rp_Binary_Rel c a b})
    (hq : 0 < q.toMeasure {b | rp_Binary_Rel c a b}) :
    Integrable (fun st => rp_Replication_W_KL c (a, st)) ((rp_Replication_iid p).prod (rp_Replication_iid q)) ∧
      (∫ st, rp_Replication_W_KL c (a, st) ∂(rp_Replication_iid p).prod (rp_Replication_iid q)) =
        Real.log (p.toMeasure {b | rp_Binary_Rel c a b}).toReal -
          Real.log (q.toMeasure {b | rp_Binary_Rel c a b}).toReal := by
  let E : Set R := {b | rp_Binary_Rel c a b}
  have hE : MeasurableSet E := (Set.toFinite E).measurableSet
  have hn := (iid_harmonic_integrable q E hE hq).comp_snd (rp_Replication_iid p)
  have hs := (iid_harmonic_integrable p E hE hp).comp_fst (rp_Replication_iid q)
  have hae :
      (fun st => rp_Replication_W_KL c (a, st)) =ᵐ[(rp_Replication_iid p).prod (rp_Replication_iid q)]
        (fun st =>
          rp_Replication_H ((rp_Replication_firstHit (fun n => st.2 n ∈ E)).toNat - 1) -
            rp_Replication_H ((rp_Replication_firstHit (fun n => st.1 n ∈ E)).toNat - 1)) := by
    filter_upwards [streams_null_finite c p q a hq,
      streams_specific_finite c p q a hp] with st hnt hst
    change rp_Replication_W_KL c (a, st) =
      rp_Replication_H ((rp_Replication_R_null c (a, st)).toNat - 1) - rp_Replication_H ((rp_Replication_R_specific c (a, st)).toNat - 1)
    simp only [if_pos hc, if_neg (not_or.mpr ⟨hnt, hst⟩)]
  refine ⟨(hn.sub hs).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub hn hs,
    integral_fun_snd (μ := rp_Replication_iid p) (ν := rp_Replication_iid q)
      (fun t : ℕ → R => rp_Replication_H ((rp_Replication_firstHit (fun n => t n ∈ E)).toNat - 1)),
    integral_fun_fst (μ := rp_Replication_iid p) (ν := rp_Replication_iid q)
      (fun s : ℕ → R => rp_Replication_H ((rp_Replication_firstHit (fun n => s n ∈ E)).toNat - 1)),
    iid_harmonic_integral q E hE hq, iid_harmonic_integral p E hE hp]
  simp
  ring

variable {X : Type}

omit [Fintype R] in
/-- Positive task and anchor atoms give positive success probabilities for
both searches. No support condition is imposed elsewhere. -/
theorem anchor_target_probabilities (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) (x : X) (hx : 0 < P x)
    (a : R) (ha : 0 < k x a) :
    0 < (k x).toMeasure {b | rp_Binary_Rel c a b} ∧
      0 < (P.bind k).toMeasure {b | rp_Binary_Rel c a b} := by
  have ha' : a ∈ (P.bind k).support := by
    rw [PMF.mem_support_bind_iff]
    exact ⟨x, ne_of_gt hx, ne_of_gt ha⟩
  exact ⟨target_pos c hc (k x) a ha,
    target_pos c hc (P.bind k) a (pos_iff_ne_zero.mpr ha')⟩

theorem conditional_pearson_integrable (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) (x : X) (hx : 0 < P x) :
    Integrable (rp_Replication_W_chiSquared c) (rp_Replication_conditionalTranscriptLaw P k x) := by
  dsimp only
  apply integrable_anchor_prod (k x) _ _ (measurable_W_chiSquared c)
  intro a ha
  exact (pearson_streams_moment c hc (k x) (P.bind k) a
    (anchor_target_probabilities c hc P k x hx a ha).2).1

theorem conditional_kl_integrable (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) (x : X) (hx : 0 < P x) :
    Integrable (rp_Replication_W_KL c) (rp_Replication_conditionalTranscriptLaw P k x) := by
  dsimp only
  apply integrable_anchor_prod (k x) _ _ (measurable_W_KL c)
  intro a ha
  obtain ⟨hp, hq⟩ := anchor_target_probabilities c hc P k x hx a ha
  exact (kl_streams_moment c hc (k x) (P.bind k) a hp hq).1

/-- Integrability of the actual Pearson payment under the full experiment,
including the invalid-critic branch and arbitrary null task/report atoms. -/
theorem integrable_W_chiSquared_impl [Fintype X] (c : Critic R)
    (P : PMF X) (k : Kernel X R) :
    Integrable (rp_Replication_W_chiSquared c) (rp_Replication_transcriptLaw P k) := by
  by_cases hc : rp_Binary_Valid c
  · exact integrable_transcriptLaw P k _ (conditional_pearson_integrable c hc P k)
  · have hz : rp_Replication_W_chiSquared c = fun _ : rp_Replication_Transcript R => (0 : ℝ) := by
      funext t
      exact (invalid_payments c hc t).1
    rw [hz]
    exact integrable_const 0

/-- Integrability of the actual harmonic difference under the full experiment.
This assertion is separate from almost-sure termination. -/
theorem integrable_W_KL_impl [Fintype X] (c : Critic R)
    (P : PMF X) (k : Kernel X R) :
    Integrable (rp_Replication_W_KL c) (rp_Replication_transcriptLaw P k) := by
  by_cases hc : rp_Binary_Valid c
  · exact integrable_transcriptLaw P k _ (conditional_kl_integrable c hc P k)
  · have hz : rp_Replication_W_KL c = fun _ : rp_Replication_Transcript R => (0 : ℝ) := by
      funext t
      exact (invalid_payments c hc t).2
    rw [hz]
    exact integrable_const 0

theorem conditional_pearson_integral (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) (x : X) (hx : 0 < P x) :
    (∫ t, rp_Replication_W_chiSquared c t ∂rp_Replication_conditionalTranscriptLaw P k x) =
      ∑ a, mass (k x) a *
        ((k x).toMeasure {b | rp_Binary_Rel c a b}).toReal *
          ((P.bind k).toMeasure {b | rp_Binary_Rel c a b}).toReal⁻¹ - 1 := by
  have he :
      (∫ t, rp_Replication_W_chiSquared c t ∂rp_Replication_conditionalTranscriptLaw P k x) =
        ∑ a, mass (k x) a *
          (((k x).toMeasure {b | rp_Binary_Rel c a b}).toReal *
            ((P.bind k).toMeasure {b | rp_Binary_Rel c a b}).toReal⁻¹ - 1) := by
    rw [
      integral_prod _ (conditional_pearson_integrable c hc P k x hx),
      integral_pmf_fintype]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : k x a = 0
    · simp [mass, ha]
    · rw [(pearson_streams_moment c hc (k x) (P.bind k) a
        (anchor_target_probabilities c hc P k x hx a
          (pos_iff_ne_zero.mpr ha)).2).2]
  rw [he]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, mass_sum, mul_assoc]

theorem conditional_kl_integral (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) (x : X) (hx : 0 < P x) :
    (∫ t, rp_Replication_W_KL c t ∂rp_Replication_conditionalTranscriptLaw P k x) =
      ∑ a, mass (k x) a *
        (Real.log ((k x).toMeasure {b | rp_Binary_Rel c a b}).toReal -
          Real.log ((P.bind k).toMeasure {b | rp_Binary_Rel c a b}).toReal) := by
  rw [
    integral_prod _ (conditional_kl_integrable c hc P k x hx),
    integral_pmf_fintype]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : k x a = 0
  · simp [mass, ha]
  · obtain ⟨hp, hq⟩ := anchor_target_probabilities c hc P k x hx a
      (pos_iff_ne_zero.mpr ha)
    rw [(kl_streams_moment c hc (k x) (P.bind k) a hp hq).2]

/-- Actual Pearson expectation reduced to class success probabilities.
Identifying this expression with normalized agreement is a later algebra step. -/
theorem u_chiSquared_class_sum [Fintype X] (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) :
    rp_Replication_u_chiSquared c P k =
      ∑ x, mass P x *
        ((∑ a, mass (k x) a *
          ((k x).toMeasure {b | rp_Binary_Rel c a b}).toReal *
            ((P.bind k).toMeasure {b | rp_Binary_Rel c a b}).toReal⁻¹) - 1) := by
  refine (integral_transcriptLaw P k (rp_Replication_W_chiSquared c)
    (conditional_pearson_integrable c hc P k)).trans ?_
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x = 0
  · simp [mass, hx]
  · exact congrArg (fun z : ℝ => mass P x * z)
      (conditional_pearson_integral c hc P k x (pos_iff_ne_zero.mpr hx))

/-- Actual KL expectation reduced to conditional-minus-marginal class logs.
This is still a statement about the original Bochner integral. -/
theorem u_KL_class_sum [Fintype X] (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) :
    rp_Replication_u_KL c P k =
      ∑ x, mass P x * ∑ a, mass (k x) a *
        (Real.log ((k x).toMeasure {b | rp_Binary_Rel c a b}).toReal -
          Real.log ((P.bind k).toMeasure {b | rp_Binary_Rel c a b}).toReal) := by
  refine (integral_transcriptLaw P k (rp_Replication_W_KL c)
    (conditional_kl_integrable c hc P k)).trans ?_
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x = 0
  · simp [mass, hx]
  · exact congrArg (fun z : ℝ => mass P x * z)
      (conditional_kl_integral c hc P k x (pos_iff_ne_zero.mpr hx))

end MutualEvaluation.Replication
end