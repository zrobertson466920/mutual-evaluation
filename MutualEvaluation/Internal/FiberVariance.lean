import Mathlib

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-! Finite weighted aggregation used by the self-evaluation proofs. -/
noncomputable section
namespace MutualEvaluation.Fiber

variable {A B : Type} [Fintype A]
attribute [local instance] Classical.propDecidable

def push (g : A → B) (w : A → ℝ) (b : B) : ℝ :=
  ∑ a, if g a = b then w a else 0

def mean (g : A → B) (w q : A → ℝ) (b : B) : ℝ :=
  push g (fun a => w a * q a) b / push g w b

theorem push_mul [Fintype B] (g : A → B) (w : A → ℝ) (h : B → ℝ) :
    ∑ b, push g w b * h b = ∑ a, w a * h (g a) := by
  simp only [push, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem weight_le_push (g : A → B) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (a : A) :
    w a ≤ push g w (g a) := by
  have h := Finset.single_le_sum
    (f := fun x => if g x = g a then w x else 0)
    (fun x (_ : x ∈ Finset.univ) => by
      split_ifs
      · exact hw x
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa [push] using h

theorem weight_zero (g : A → B) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (a : A) (hz : push g w (g a) = 0) : w a = 0 :=
  le_antisymm (hz ▸ weight_le_push g w hw a) (hw a)

theorem mass_mul_mean (g : A → B) (w q : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (b : B) :
    push g w b * mean g w q b = push g (fun a => w a * q a) b := by
  by_cases hb : push g w b = 0
  · have hz : push g (fun a => w a * q a) b = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      split_ifs with ha
      · change w a * q a = 0
        have hwz := weight_zero g w hw a (ha.symm ▸ hb)
        rw [hwz, zero_mul]
      · rfl
    simp [mean, hb, hz]
  · dsimp [mean]
    field_simp

/-- Weighted ANOVA, including zero-mass and empty fibers. -/
theorem decomposition [Fintype B] (g : A → B) (w q : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (t : ℝ) :
    ∑ a, w a * (q a - t)^2 =
      (∑ b, push g w b * (mean g w q b - t)^2) +
        ∑ a, w a * (q a - mean g w q (g a))^2 := by
  let m := mean g w q
  have hcross :
      ∑ a, w a * q a * (m (g a) - t) =
        ∑ a, w a * m (g a) * (m (g a) - t) := by
    rw [← push_mul g (fun a => w a * q a) (fun b => m b - t)]
    simp only [mul_assoc]
    rw [← push_mul g w (fun b => m b * (m b - t))]
    apply Finset.sum_congr rfl
    intro b _
    rw [← mass_mul_mean g w q hw b]
    dsimp [m]
    ring
  rw [push_mul g w (fun b => (mean g w q b - t)^2), ← Finset.sum_add_distrib]
  have hterm (a : A) : w a * (q a - t)^2 =
      (w a * (m (g a) - t)^2 + w a * (q a - m (g a))^2) +
        2 * (w a * q a * (m (g a) - t) -
          w a * m (g a) * (m (g a) - t)) := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hcross]
  simp [m]

theorem loss_nonneg (g : A → B) (w q : A → ℝ) (hw : ∀ a, 0 ≤ w a) :
    0 ≤ ∑ a, w a * (q a - mean g w q (g a))^2 :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (sq_nonneg _))

private theorem loss_zero_iff_mean (g : A → B) (w q : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    (∑ a, w a * (q a - mean g w q (g a))^2) = 0 ↔
      ∀ a, 0 < w a → q a = mean g w q (g a) := by
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a ∈ Finset.univ) => mul_nonneg (hw a) (sq_nonneg _))]
  constructor
  · intro h a ha
    have hz := (mul_eq_zero.mp (h a (Finset.mem_univ a))).resolve_left (ne_of_gt ha)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h a _
    by_cases ha : w a = 0
    · simp [ha]
    · rw [h a (lt_of_le_of_ne (hw a) (Ne.symm ha))]
      simp

theorem loss_zero_iff (g : A → B) (w q : A → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ a, w a * (q a - mean g w q (g a))^2) = 0 ↔
      ∀ a b, g a = g b → 0 < w a → 0 < w b → q a = q b := by
  rw [loss_zero_iff_mean g w q hw]
  constructor
  · intro h a b hab ha hb
    rw [h a ha, h b hb, hab]
  · intro h a ha
    have hp : 0 < push g w (g a) := ha.trans_le (weight_le_push g w hw a)
    have hn : push g (fun b => w b * q b) (g a) = push g w (g a) * q a := by
      simp only [push, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : g b = g a
      · simp only [if_pos hb]
        by_cases hz : w b = 0
        · simp [hz]
        · rw [h b a hb (lt_of_le_of_ne (hw b) (Ne.symm hz)) ha]
      · simp [hb]
    dsimp [mean]
    rw [hn, mul_div_cancel_left₀ _ (ne_of_gt hp)]

end MutualEvaluation.Fiber
end