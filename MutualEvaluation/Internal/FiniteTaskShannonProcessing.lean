import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.FiniteTaskShannon
import MutualEvaluation.Internal.FiniteTaskProcessing

/-!
INTERNAL / DRAFT — Shannon information under fixed stochastic reporting.
The proof retains the original report alongside the processed output and then
uses deterministic annotation. All information quantities are finite sums.
No loop expectation, integrability, or unbiasedness certificate occurs here.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.FiniteTask
open Probability

variable {X R B : Type}

/-- Auxiliary experiment retaining both input and output of the reporting channel.
This is proof support, not a new operational replication interface. -/
private def reportingExtension (k : Kernel X R) (τ : Kernel R B) : Kernel X (R × B) :=
  fun x => (k x).bind fun a => (τ a).map fun b => (a, b)

private theorem extension_fst (k : Kernel X R) (τ : Kernel R B) :
    rp_FiniteTask_annotated (reportingExtension k τ) Prod.fst = k := by
  funext x
  simp only [ reportingExtension, PMF.map, Function.comp_def,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_const, PMF.bind_pure]

private theorem extension_snd (k : Kernel X R) (τ : Kernel R B) :
    rp_FiniteTask_annotated (reportingExtension k τ) Prod.snd = (fun x => (k x).bind τ) := by
  funext x
  simp only [ reportingExtension, PMF.map, Function.comp_def,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]

variable (P : PMF X) (k : Kernel X R) (τ : Kernel R B)
variable [Fintype X] [Fintype R] [Fintype B]

omit [Fintype X] in
private theorem extension_jointMass (x : X) (a : R) (b : B) :
    rp_FiniteTask_jointMass P (reportingExtension k τ) x (a, b) =
      rp_FiniteTask_jointMass P k x a * mass (τ a) b := by
  classical
  have hm : mass (reportingExtension k τ x) (a, b) =
      mass (k x) a * mass (τ a) b := by
    change mass ((k x).bind fun r => (τ r).bind fun s => PMF.pure (r, s)) (a, b) = _
    simp only [mass_bind, mass_pure, Prod.mk.injEq]
    simp [ite_and]
  simp only [ hm, mul_assoc]

private theorem extension_reportMass (a : R) (b : B) :
    rp_FiniteTask_reportMass P (reportingExtension k τ) (a, b) =
      rp_FiniteTask_reportMass P k a * mass (τ a) b := by
  calc
    _ = ∑ x, rp_FiniteTask_jointMass P k x a * mass (τ a) b := by
      simp only [reportMass_eq_sum, extension_jointMass]
    _ = _ := by rw [← Finset.sum_mul, ← reportMass_eq_sum]

private theorem extension_posterior (a : R) (b : B) (hb : mass (τ a) b ≠ 0) :
    rp_FiniteTask_posterior P (reportingExtension k τ) (a, b) = rp_FiniteTask_posterior P k a := by
  funext x
  simp only [ extension_jointMass, extension_reportMass]
  exact mul_div_mul_right _ _ hb

/-- Recording a fresh randomized output alongside its input loses no task
information. Support is checked only where the joint report has positive mass. -/
private theorem shannon_extension :
    rp_FiniteTask_shannon P (reportingExtension k τ) = rp_FiniteTask_shannon P k := by
  have he :
      rp_FiniteTask_shannon P (reportingExtension k τ) =
        rp_FiniteTask_shannon P (rp_FiniteTask_annotated (reportingExtension k τ) Prod.fst) := by
    apply (shannon_annotation_eq_iff P (reportingExtension k τ) Prod.fst).2
    rintro ⟨a, b⟩ hab
    have hb : mass (τ a) b ≠ 0 := by
      intro hz
      rw [extension_reportMass, hz, mul_zero] at hab
      exact (lt_irrefl 0) hab
    rw [extension_fst]
    exact extension_posterior P k τ a b hb
  simpa only [extension_fst] using he

/-- Exact stochastic-reporting loss as a weighted divergence between the
input and output task posteriors. Null transition atoms contribute zero. -/
theorem shannon_processing_loss :
    rp_FiniteTask_shannon P k - rp_FiniteTask_shannon P (fun x => (k x).bind τ) =
      ∑ a, ∑ b, rp_FiniteTask_reportMass P k a * mass (τ a) b *
        rp_FiniteLog_divergence (rp_FiniteTask_posterior P k a)
          (rp_FiniteTask_posterior P (fun x => (k x).bind τ) b) := by
  have hl := shannon_annotation_loss P (reportingExtension k τ) Prod.snd
  rw [shannon_extension, extension_snd] at hl
  rw [hl]
  simp only [Fintype.sum_prod_type, extension_snd]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : mass (τ a) b = 0
  · simp only [extension_reportMass, hb, mul_zero, zero_mul]
  · have he := congrArg
      (fun posterior : X → ℝ =>
        rp_FiniteTask_reportMass P (reportingExtension k τ) (a, b) *
          rp_FiniteLog_divergence posterior
            (rp_FiniteTask_posterior P (fun x => (k x).bind τ) b))
      (extension_posterior P k τ a b hb)
    simpa only [extension_reportMass] using he

/-- Shannon task information cannot increase under stochastic reporting.
The finite input and output alphabets may differ; full support is unnecessary. -/
theorem shannon_data_processing :
    rp_FiniteTask_shannon P (fun x => (k x).bind τ) ≤ rp_FiniteTask_shannon P k := by
  calc
    _ = rp_FiniteTask_shannon P (rp_FiniteTask_annotated (reportingExtension k τ) Prod.snd) := by
      rw [extension_snd]
    _ ≤ rp_FiniteTask_shannon P (reportingExtension k τ) :=
      shannon_annotation_mono P (reportingExtension k τ) Prod.snd
    _ = _ := shannon_extension P k τ

omit [Fintype R] in
/-- Deterministic coarsening of the critic's annotation classes. -/
theorem shannon_annotation_coarsen {C : Type} [Fintype C]
    (g : R → B) (h : B → C) :
    rp_FiniteTask_shannon P (rp_FiniteTask_annotated k (h ∘ g)) ≤ rp_FiniteTask_shannon P (rp_FiniteTask_annotated k g) := by
  rw [← annotated_comp]
  exact shannon_annotation_mono P (rp_FiniteTask_annotated k g) h

end MutualEvaluation.FiniteTask
end