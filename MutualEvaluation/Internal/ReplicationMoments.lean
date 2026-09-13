import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationRecurrence
import Mathlib.Probability.Distributions.Geometric

/-!
INTERNAL — first moment of the actual stream-defined first-hit clock.

The geometric measure below is a derived pushforward law, not an assumed
replacement for the sampling experiment. Positivity concerns one measurable
success event; no full-support assumption is made on the report distribution.
The real call count uses toNat's zero extension at infinity, a null event under
the positivity hypothesis. Payment integrability and unbiasedness still require
lifting these stream results through the anchor and task mixture.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open MeasureTheory ProbabilityTheory
open Internal.ReplicationPaths

variable {R : Type} [MeasurableSpace R]

/-- Internal integration coordinate: failures before the first success.
Its value on a nonterminating stream is zero. -/
def hitFailures (E : Set R) (ω : ℕ → R) : ℕ :=
  (rp_Replication_firstHit (fun n => ω n ∈ E)).toNat - 1

theorem measurable_hitFailures (E : Set R) (hE : MeasurableSet E) :
    Measurable (hitFailures E) :=
  (measurable_of_countable (fun n : ℕ∞ => n.toNat - 1)).comp
    (measurable_firstHit (fun (ω : ℕ → R) n => ω n ∈ E)
      (fun n => hE.preimage (measurable_pi_apply n)))

omit [MeasurableSpace R] in
theorem hitFailures_eq_iff (E : Set R) (ω : ℕ → R)
    (hω : rp_Replication_firstHit (fun m => ω m ∈ E) ≠ ⊤) (n : ℕ) :
    hitFailures E ω = n ↔
      rp_Replication_firstHit (fun m => ω m ∈ E) = ((n + 1 : ℕ) : ℕ∞) := by
  classical
  have hs : ∃ m, ω m ∈ E := by
    by_contra h
    exact hω (by simp [ h])
  have ht (m : ℕ) : (m : ℕ∞).toNat = m := by simp
  calc
    hitFailures E ω = n ↔ Nat.find hs = n := by
      simp only [hitFailures, dif_pos hs, ht, Nat.add_sub_cancel]
    _ ↔ rp_Replication_firstHit (fun m => ω m ∈ E) = ((n + 1 : ℕ) : ℕ∞) := by
      simp [ hs]

/-- The success parameter is computed from the actual call distribution. -/
def hitParameter (p : PMF R) (E : Set R) : unitInterval :=
  ⟨(p.toMeasure E).toReal, ENNReal.toReal_nonneg, by
    have h : p.toMeasure E ≤ 1 := by
      calc
        p.toMeasure E ≤ p.toMeasure Set.univ := measure_mono (Set.subset_univ E)
        _ = 1 := measure_univ
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h⟩

theorem hitParameter_ne_zero (p : PMF R) (E : Set R)
    (hp : 0 < p.toMeasure E) : hitParameter p E ≠ 0 := by
  intro he
  have hz : (p.toMeasure E).toReal = 0 :=
    congrArg (fun q : unitInterval => (q : ℝ)) he
  exact (ne_of_gt (ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _))) hz

/-- The failure count's law is proved from first-hit cylinder events and
almost-sure termination. The success-one boundary is included. -/
theorem iid_hitFailures_map (p : PMF R) (E : Set R)
    (hE : MeasurableSet E) (hp : 0 < p.toMeasure E) :
    (rp_Replication_iid p).map (hitFailures E) = geometricMeasure (hitParameter p E) := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (measurable_hitFailures E hE) (measurableSet_singleton n),
    geometricMeasure_singleton (hitParameter_ne_zero p E hp)]
  calc
    rp_Replication_iid p ((hitFailures E) ⁻¹' {n}) =
        rp_Replication_iid p {ω | rp_Replication_firstHit (fun m => ω m ∈ E) = ((n + 1 : ℕ) : ℕ∞)} := by
      apply measure_congr
      filter_upwards [iid_first_hit_finite p E hE hp] with ω hω
      exact propext (hitFailures_eq_iff E ω hω n)
    _ = p.toMeasure E * (p.toMeasure Eᶜ)^n := iid_first_hit p E hE n
    _ = ENNReal.ofReal
        ((1 - (hitParameter p E : ℝ))^n * (hitParameter p E : ℝ)) := by
      have hq : 0 ≤ 1 - (hitParameter p E : ℝ) :=
        sub_nonneg.mpr (hitParameter p E).property.2
      rw [ENNReal.ofReal_mul (pow_nonneg hq n), ENNReal.ofReal_pow hq,
        ENNReal.ofReal_sub _ (hitParameter p E).property.1]
      simp only [hitParameter, ENNReal.ofReal_one,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [measure_compl hE (measure_ne_top _ _), measure_univ]
      exact mul_comm _ _

/-- Analytic series used only after the stream law has been identified. -/
theorem geometric_calls_hasSum (q : unitInterval) (hq : q ≠ 0) :
    HasSum (fun n : ℕ => (1 - (q : ℝ))^n * (q : ℝ) * ((n : ℝ) + 1))
      (q : ℝ)⁻¹ := by
  have hq0 : (q : ℝ) ≠ 0 := by
    intro h
    exact hq (Subtype.ext h)
  have hpos : 0 < (q : ℝ) :=
    lt_of_le_of_ne q.property.1 (Ne.symm hq0)
  have hr : ‖(1 - (q : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr q.property.2)]
    linarith
  have hs : HasSum (fun n : ℕ => ((n : ℝ) + 1) * (1 - (q : ℝ))^n)
      (1 / (q : ℝ)^2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hr
  have hm := hs.mul_right (q : ℝ)
  have hv : 1 / (q : ℝ)^2 * (q : ℝ) = (q : ℝ)⁻¹ := by
    field_simp
  rw [hv] at hm
  have he :
      (fun n : ℕ => ((n : ℝ) + 1) * (1 - (q : ℝ))^n * (q : ℝ)) =
        (fun n : ℕ => (1 - (q : ℝ))^n * (q : ℝ) * ((n : ℝ) + 1)) := by
    funext n
    ring
  rw [he] at hm
  exact hm

theorem geometric_calls_integrable (q : unitInterval) (hq : q ≠ 0) :
    Integrable (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure q) := by
  apply (integrable_geometricMeasure_iff hq).2
  apply (geometric_calls_hasSum q hq).summable.congr
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]

theorem geometric_calls_integral (q : unitInterval) (hq : q ≠ 0) :
    (∫ n : ℕ, (n : ℝ) + 1 ∂geometricMeasure q) = (q : ℝ)⁻¹ := by
  rw [integral_geometricMeasure' hq (geometric_calls_integrable q hq)]
  simpa only [smul_eq_mul] using (geometric_calls_hasSum q hq).tsum_eq

theorem hitFailures_add_one_ae (p : PMF R) (E : Set R)
    (hE : MeasurableSet E) (hp : 0 < p.toMeasure E) :
    ∀ᵐ ω ∂rp_Replication_iid p, (hitFailures E ω : ℝ) + 1 =
      ((rp_Replication_firstHit (fun n => ω n ∈ E)).toNat : ℝ) := by
  filter_upwards [iid_first_hit_finite p E hE hp] with ω hω
  have he := (hitFailures_eq_iff E ω hω (hitFailures E ω)).1 rfl
  have ht (m : ℕ) : (m : ℕ∞).toNat = m := by simp
  have hn : (rp_Replication_firstHit (fun n => ω n ∈ E)).toNat =
      hitFailures E ω + 1 :=
    (congrArg (fun n : ℕ∞ => n.toNat) he).trans
      (ht (hitFailures E ω + 1))
  simpa only [Nat.cast_add, Nat.cast_one] using
    (congrArg (fun n : ℕ => (n : ℝ)) hn).symm

/-- Integrability of the actual number of calls, with its zero extension on
nontermination. This is stronger than almost-sure termination alone. -/
theorem iid_firstHit_integrable (p : PMF R) (E : Set R)
    (hE : MeasurableSet E) (hp : 0 < p.toMeasure E) :
    Integrable (fun ω => ((rp_Replication_firstHit (fun n => ω n ∈ E)).toNat : ℝ)) (rp_Replication_iid p) := by
  have hg := geometric_calls_integrable (hitParameter p E) (hitParameter_ne_zero p E hp)
  rw [← iid_hitFailures_map p E hE hp] at hg
  have hi : Integrable (fun ω => (hitFailures E ω : ℝ) + 1) (rp_Replication_iid p) :=
    (integrable_map_measure
      (measurable_of_countable (fun n : ℕ => (n : ℝ) + 1)).aestronglyMeasurable
      (measurable_hitFailures E hE).aemeasurable).1 hg
  exact hi.congr (hitFailures_add_one_ae p E hE hp)

/-- Reciprocal-probability first moment derived for the stream-defined clock,
not postulated as a waiting-time oracle. -/
theorem iid_firstHit_integral (p : PMF R) (E : Set R)
    (hE : MeasurableSet E) (hp : 0 < p.toMeasure E) :
    (∫ ω, ((rp_Replication_firstHit (fun n => ω n ∈ E)).toNat : ℝ) ∂rp_Replication_iid p) =
      (p.toMeasure E).toReal⁻¹ := by
  calc
    _ = ∫ ω, (hitFailures E ω : ℝ) + 1 ∂rp_Replication_iid p :=
      integral_congr_ae (by
        filter_upwards [hitFailures_add_one_ae p E hE hp] with ω hω
        exact hω.symm)
    _ = ∫ n : ℕ, (n : ℝ) + 1 ∂(rp_Replication_iid p).map (hitFailures E) :=
      (integral_map_of_stronglyMeasurable (measurable_hitFailures E hE)
        (measurable_of_countable (fun n : ℕ => (n : ℝ) + 1)).stronglyMeasurable).symm
    _ = (p.toMeasure E).toReal⁻¹ := by
      rw [iid_hitFailures_map p E hE hp, geometric_calls_integral _ (hitParameter_ne_zero p E hp)]
      rfl

end MutualEvaluation.Replication
end