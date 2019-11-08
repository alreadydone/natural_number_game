import mynat.le
import solutions.world2_multiplication
import tactic.interactive

-- #check tactic.interactive.rintro 
meta def less_leaky.interactive.rintro := tactic.interactive.rintro

namespace mynat

-- example
theorem le_refl (a : mynat) : a ≤ a :=
begin
  use 0,
  rw add_zero,
end

example : one ≤ one := le_refl one

-- ignore this; it's making the "refl" tactic work with goals of the form a ≤ a
attribute [_refl_lemma] le_refl

theorem le_succ {a b : mynat} (h : a ≤ b) : a ≤ (succ b) :=
begin
  cases h with c h,
  use succ c,
  rw add_succ, rw h,
end


lemma zero_le (a : mynat) : 0 ≤ a :=
begin
  use a, rw zero_add,
end

lemma le_zero {a : mynat} : a ≤ 0 → a = 0 :=
begin
  intro h,
  cases h with b h,
  apply add_right_eq_zero,
  exact eq.symm h,
/-
  intro h,
  cases h with b h,
  cases a with a,
   refl,
   rw succ_add at h,
   apply absurd (eq.symm h),
   apply succ_ne_zero,
  -/
end

theorem le_trans ⦃a b c : mynat⦄ (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
  cases hab with d hab,
  cases hbc with e hbc,
  use d+e,
  rw hab at hbc,
  rw hbc,
  apply add_assoc,
end

instance : preorder mynat := by structure_helper

-- ignore this, it's the definition.
theorem lt_iff_le_not_le {a b : mynat} : a < b ↔ a ≤ b ∧ ¬ b ≤ a := iff.rfl

theorem le_antisymm : ∀ {{a b : mynat}}, a ≤ b → b ≤ a → a = b :=
begin
  intros a b hab hba,
  cases hab with c hab,
  cases hba with d hba,
  rw hba at hab,
  rw add_assoc at hab,
  rw add_right_eq_zero (eq_zero_of_add_right_eq_self (eq.symm hab)) at hba,
  rw add_zero at hba, exact hba,
end

instance : partial_order mynat := by structure_helper

theorem lt_iff_le_and_ne ⦃a b : mynat⦄ : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  split,
   intro h,
   cases h with h1 h2,
   split,
    exact h1,
    intro h,
    rw h at h2,
    exact h2 (le_refl b),
   intro h,
   split,
    cases h with h _, exact h,
    cases h with h1 h2,
    intro h,
    exact h2 (le_antisymm h1 h),
end


lemma succ_le_succ {a b : mynat} (h : a ≤ b) : succ a ≤ succ b :=
begin
  cases h with c h,
  use c, rw succ_add, rw h,
end

theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=
begin
  revert a,
  induction b with b h,
    intro a, right, apply zero_le,
    intro a, cases a with a,
      left, apply zero_le,
      cases h a with h1 h2,
        left, exact succ_le_succ h1,
        right, exact succ_le_succ h2,
end

instance : linear_order mynat := by structure_helper


theorem add_le_add_right (a b : mynat) : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin
  intros h t,
  cases h with c h,
  use c,
  rw h,
  rw add_right_comm,
end

theorem le_succ_self (a : mynat) : a ≤ succ a :=
begin
  use 1, rw succ_eq_add_one,
end

theorem le_of_succ_le_succ {a b : mynat} : succ a ≤ succ b → a ≤ b :=
begin
  intro h,
  cases h with c h,
  use c,
  rw succ_add at h,
  exact succ_inj h,
/-
  repeat {rw succ_eq_add_one at h},
  rw add_right_comm at h,
  exact (add_right_cancel h),
-/
end

theorem not_succ_le_self {{d : mynat}} (h : succ d ≤ d) : false :=
begin
  cases h with c h,
  rw succ_add at h,
  rw ← add_succ at h,
  apply zero_ne_succ,
  symmetry,
  exact eq_zero_of_add_right_eq_self (eq.symm h),
end

theorem add_le_add_left : ∀ (a b : mynat), a ≤ b → ∀ (c : mynat), c + a ≤ c + b :=
begin
  intros a b h c,
  rw add_comm c a,
  rw add_comm c b,
  apply add_le_add_right,
  exact h,
end

def succ_le_succ_iff (a b : mynat) : succ a ≤ succ b ↔ a ≤ b :=
begin
  split,
    exact le_of_succ_le_succ,
    exact succ_le_succ,
end

-- convenient lemma
def lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b :=
begin
  split,
    intro h,
    cases h with h1 h2,
    cases h1 with c h1,
    cases c with c,
      rw mynat_zero_eq_zero at h1,
      rw add_zero at h1,
      rw h1 at h2,
      apply absurd (le_refl a) h2,
      use c,
      rw succ_add, rw ← add_succ, exact h1,
    intro h,
    split,
      cases h with c h,
      use (succ c),
      rw add_succ, rw ← succ_add, exact h,
      intro h1,
      exact not_succ_le_self (le_trans h h1),
end

def succ_lt_succ_iff (a b : mynat) : succ a < succ b ↔ a < b :=
begin
  repeat {rw lt_iff_succ_le},
  exact succ_le_succ_iff (succ a) b,
/-
  split,
    intro h,
    cases h with h1 h2,
    split,
      apply le_of_succ_le_succ h1,
      intro h, exact h2 (succ_le_succ h),
    intro h,
    cases h with h1 h2,
    split,
      apply succ_le_succ h1,
      intro h, exact h2 (le_of_succ_le_succ h),
-/
end


theorem le_of_add_le_add_left ⦃ a b c : mynat⦄ : a + b ≤ a + c → b ≤ c :=
begin
  intro h,
  cases h with d h,
  use d,
  rw add_assoc at h,
  exact add_left_cancel h,
end

theorem lt_of_add_lt_add_left : ∀ {{a b c : mynat}}, a + b < a + c → b < c :=
begin
  intros a b c,
  repeat {rw lt_iff_succ_le},
  rw ← add_succ,
  intro h,
  exact le_of_add_le_add_left h,
end

theorem le_iff_exists_add : ∀ (a b : mynat), a ≤ b ↔ ∃ (c : mynat), b = a + c :=
begin
  exact le_def,
end

theorem zero_ne_one : (0 : mynat) ≠ 1 :=
begin
  exact zero_ne_succ 0,
end

instance : ordered_comm_monoid mynat := by structure_helper

instance : ordered_cancel_comm_monoid mynat := by structure_helper

-- removed redundant condition 0 ≤ c
theorem mul_le_mul_of_nonneg_left ⦃a b c : mynat⦄ : a ≤ b → c * a ≤ c * b :=
begin
  intros h,
  cases h with d h,
  rw h, rw mul_add,
  use c*d,
end

theorem mul_le_mul_of_nonneg_right ⦃a b c : mynat⦄ : a ≤ b → a * c ≤ b * c :=
begin
  rw mul_comm a c, rw mul_comm b c,
  apply mul_le_mul_of_nonneg_left,
end

theorem ne_zero_of_pos ⦃a : mynat⦄ : 0 < a → a ≠ 0 :=
begin
  rw lt_iff_le_and_ne,
  intros h,
  cases h with _ h,
  symmetry, exact h,
end

theorem mul_lt_mul_of_pos_left ⦃a b c : mynat⦄ : a < b → 0 < c → c * a < c * b :=
begin
  intros h hc,
  rw lt_iff_succ_le at h hc ⊢, rw succ_eq_add_one,
  apply le_trans (add_le_add_left 1 c hc (c*a)),
  rw ← mul_succ,
  exact mul_le_mul_of_nonneg_left h,
end

theorem mul_lt_mul_of_pos_right ⦃a b c : mynat⦄ : a < b → 0 < c → a * c < b * c :=
begin
  rw mul_comm a c, rw mul_comm b c,
  apply mul_lt_mul_of_pos_left,
end

instance : ordered_semiring mynat := by structure_helper

lemma lt_irrefl (a : mynat) : ¬ (a < a) :=
begin
  intro h,
  cases h with h1 h2,
  exact h2 h1,
end

theorem not_lt_zero ⦃a : mynat⦄ : ¬(a < 0) :=
begin
  intro h,
  rw lt_iff_succ_le at h,
  exact not_succ_le_self (le_trans h (zero_le a)),
end

theorem lt_succ_self (n : mynat) : n < succ n :=
begin
  rw lt_iff_succ_le,
end

theorem lt_succ_iff (m n : mynat) : m < succ n ↔ m ≤ n :=
begin
  rw lt_iff_succ_le,
  exact succ_le_succ_iff m n,
end

-- lemma necessary for the second approach to strong_induction below
theorem le_if_eq_or_lt (m n : mynat) : m ≤ n ↔ m < n ∨ m = n :=
begin
  split,
    intro h,
    cases h with c h,
    cases c with c,
      right, rw [mynat_zero_eq_zero, add_zero] at h, symmetry, exact h,
      left, rw [add_succ, ← succ_add] at h, rw lt_iff_succ_le, use c, exact h,
    intro h, cases h,
      rw lt_iff_le_not_le at h, cases h with h _, exact h,
      rw h,
end

theorem strong_induction (P : mynat → Prop)
  (IH : ∀ m : mynat, (∀ d : mynat, d < m → P d) → P m) :
  ∀ n, P n :=
begin [less_leaky]
  intro n,
  apply IH,
  induction n with n h,
    intros d ltz, exfalso, exact not_lt_zero ltz,
    {
      intros d h1,
      rw lt_succ_iff at h1,
      apply IH,
      intros e h2,
      apply h,
      rw lt_iff_succ_le at h2 ⊢,
      exact le_trans h2 h1,
      -- without appeal to lt_of_lt_of_le (external reference)
/-
    rw [lt_succ_iff, le_if_eq_or_lt] at h1,
    cases h1,
      exact h d h1,
      rw h1,
      exact IH n h,
-/
    }
end

end mynat

/-
instance : canonically_ordered_comm_semiring mynat :=
{ add := (+),
  add_assoc := add_assoc,
  zero := 0,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  le := (≤),
  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm,
  add_le_add_left := add_le_add_left,
  lt_of_add_lt_add_left := lt_of_add_lt_add_left,
  bot := 0,
  bot_le := zero_le,
  le_iff_exists_add := le_iff_exists_add,
  mul := (*),
  mul_assoc := mul_assoc,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  left_distrib := left_distrib,
  right_distrib := right_distrib,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  mul_comm := mul_comm,
  zero_ne_one := zero_ne_one,
  mul_eq_zero_iff := mul_eq_zero_iff }
-/
