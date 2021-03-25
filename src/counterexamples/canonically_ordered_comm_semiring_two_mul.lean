/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.zmod.basic
import ring_theory.subsemiring
import algebra.ordered_monoid
/-!

A `canonically_ordered_comm_semiring` with two different elements `a` and `b` such that
`a ≠ b` and `2 * a = 2 * b`.

Reference:
https://
leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/canonically_ordered.20pathology
-/

namespace from_Bhavik

/--  Bhavik Mehta's example. -/
@[derive [comm_semiring]]
def K : Type := subsemiring.closure ({1.5} : set ℚ)

instance : has_coe K ℚ := ⟨λ x, x.1⟩

instance inhabited_K : inhabited K := ⟨0⟩

instance : preorder K :=
{ le := λ x y, x = y ∨ (x : ℚ) + 1 ≤ (y : ℚ),
  le_refl := λ x, or.inl rfl,
  le_trans := λ x y z xy yz,
  begin
    rcases xy with (rfl | _), { apply yz },
    rcases yz with (rfl | _), { right, apply xy },
    right,
    exact xy.trans (le_trans ((le_add_iff_nonneg_right _).mpr zero_le_one) yz)
  end }

end from_Bhavik

lemma mem_zmod_2 (a : zmod 2) : a = 0 ∨ a = 1 :=
begin
  rcases a with ⟨_ | _ | _ | _ | a_val, _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩⟩,
  { exact or.inl rfl },
  { exact or.inr rfl },
end

lemma add_self_zmod_2 (a : zmod 2) : a + a = 0 :=
begin
  rcases mem_zmod_2 a with rfl | rfl;
  refl,
end

namespace Nxzmod_2

variables {a b : ℕ × zmod 2}

instance pre_zmod_2 : partial_order (zmod 2) :=
{ le := λ x y, x = y,
  lt := λ x y, false,
  le_refl := dec_trivial,
  le_trans := dec_trivial,
  lt_iff_le_not_le := dec_trivial,
  le_antisymm := dec_trivial }

instance preN2 : partial_order (ℕ × zmod 2) :=
{ le := prod.lex (≤) (≤),
  lt := λ (a b : ℕ × zmod 2), a ≤ b ∧ ¬b ≤ a,
  le_refl := λ ⟨a, a2⟩, prod.lex.left a2 a2 rfl.le,
  le_trans := λ a b c ab bc, begin
    cases a with a a2,
    cases b with b b2,
    cases c with c c2,
    cases ab; cases bc; refine prod.lex.left a2 c2 _;
    exact (le_trans ab_h bc_h) <|> assumption <|> exact rfl.le,
  end,
  lt_iff_le_not_le := λ a b, ⟨λ h, begin
    cases a with a a2,
    cases b with b b2,
    cases h,
    refine ⟨_, _⟩,
    refine prod.lex.left a2 b2 h_left.1,
    refine λ k, h_right _,
    refine ⟨_, _⟩,
    cases k,
    exact k_h,
    exact rfl.le,
    cases k,
    cases h_left,
    cases h_left_right,
    refl,
    exact k_h,
  end, λ h, begin
    cases h with ab nab,
    cases a with a a2,
    cases b with b b2,
    refine ⟨_, _⟩,
    cases ab,
    refine ⟨ab_h, _⟩,
    dsimp,
  end⟩,
  le_antisymm := _ }

/-- The preorder relation on `ℕ × ℤ/2ℤ` where we only compare the first coordinate,
except that we leave incomparable each pair of elements with the same first component.
For instance, `∀ α, β ∈ ℤ/2ℤ`, the inequality `(1,α) ≤ (2,β)` holds,
whereas, `∀ n ∈ ℤ`, the elements `(n,0)` and `(n,1)` are incomparable. -/
instance preN2 : partial_order (ℕ × zmod 2) :=
{ le := λ x y, x = y ∨ x.1 < y.1,
  le_refl := λ a, or.inl rfl,
  le_trans := λ x y z xy yz,
  begin
    rcases xy with (rfl | _),
    { exact yz },
    { rcases yz with (rfl | _),
      { exact or.inr xy},
      { exact or.inr (xy.trans yz) } }
  end,
  le_antisymm := begin
    intros a b ab ba,
    cases ab with ab ab,
    { exact ab },
    { cases ba with ba ba,
      { exact ba.symm },
      { exact (nat.lt_asymm ab ba).elim } }
  end }

instance csrN2 : comm_semiring (ℕ × zmod 2) := by apply_instance

instance csrN2_1 : add_cancel_comm_monoid (ℕ × zmod 2) :=
{ add_left_cancel := λ a b c h, (add_right_inj a).mp h,
  add_right_cancel := λ a b c h, (add_left_inj b).mp h,
  ..Nxzmod_2.csrN2 }

/-- A strict inequality forces the first components to be different. -/
@[simp] lemma lt_def : a < b ↔ a.1 < b.1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨(rfl | a1), h1⟩,
    { exact ((not_or_distrib.mp h1).1).elim rfl },
    { exact a1 } },
  refine ⟨or.inr h, not_or_distrib.mpr ⟨λ k, _, not_lt.mpr h.le⟩⟩,
  rw k at h,
  exact nat.lt_asymm h h
end

lemma add_left_cancel : ∀ (a b c : ℕ × zmod 2), a + b = a + c → b = c :=
λ a b c h, (add_right_inj a).mp h

lemma add_le_add_left : ∀ (a b : ℕ × zmod 2), a ≤ b → ∀ (c : ℕ × zmod 2), c + a ≤ c + b :=
begin
  rintros a b (rfl | ab) c,
  { refl },
  { exact or.inr (by simpa) }
end

lemma le_of_add_le_add_left : ∀ (a b c : ℕ × zmod 2), a + b ≤ a + c → b ≤ c :=
begin
  rintros a b c (bc | bc),
  { exact le_of_eq ((add_right_inj a).mp bc) },
  { exact or.inr (by simpa using bc) }
end

lemma zero_le_one : (0 : ℕ × zmod 2) ≤ 1 := dec_trivial

lemma mul_lt_mul_of_pos_left : ∀ (a b c : ℕ × zmod 2), a < b → 0 < c → c * a < c * b :=
λ a b c ab c0, lt_def.mpr ((mul_lt_mul_left (lt_def.mp c0)).mpr (lt_def.mp ab))

lemma mul_lt_mul_of_pos_right : ∀ (a b c : ℕ × zmod 2), a < b → 0 < c → a * c < b * c :=
λ a b c ab c0, lt_def.mpr ((mul_lt_mul_right (lt_def.mp c0)).mpr (lt_def.mp ab))

instance ocsN2 : ordered_comm_semiring (ℕ × zmod 2) :=
{ add_le_add_left := add_le_add_left,
  le_of_add_le_add_left := le_of_add_le_add_left,
  zero_le_one := zero_le_one,
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right,
  ..Nxzmod_2.csrN2_1,
  ..(infer_instance : partial_order (ℕ × zmod 2)),
  ..(infer_instance : comm_semiring (ℕ × zmod 2)) }

end Nxzmod_2

namespace ex_L

open Nxzmod_2 subtype

/-- Initially, `L` was defined as the subsemiring closure of `(1,0)`. -/
def L : Type := { l : (ℕ × zmod 2) // l ≠ (0, 1) }

instance zero : has_zero L := ⟨⟨(0, 0), dec_trivial⟩⟩

instance one : has_one L := ⟨⟨(1, 1), dec_trivial⟩⟩

instance inhabited : inhabited L := ⟨1⟩

lemma add_L {a b : ℕ × zmod 2} (ha : a ≠ (0, 1)) (hb : b ≠ (0, 1)) :
  a + b ≠ (0, 1) :=
begin
  rcases a with ⟨a, a2⟩,
  rcases b with ⟨b, b2⟩,
  cases b,
  { rcases mem_zmod_2 b2 with rfl | rfl,
    { simp [ha] },
    { simpa only } },
  { simp [(a + b).succ_ne_zero] }
end

lemma mul_L {a b : ℕ × zmod 2} (ha : a ≠ (0, 1)) (hb : b ≠ (0, 1)) :
  a * b ≠ (0, 1) :=
begin
  rcases a with ⟨a, a2⟩,
  rcases b with ⟨b, b2⟩,
  cases b,
  { rcases mem_zmod_2 b2 with rfl | rfl;
    rcases mem_zmod_2 a2 with rfl | rfl;
    -- while this looks like a non-terminal `simp`, it (almost) isn't: there is only one goal where
    -- it does not finish the proof and on that goal it asks to prove `false`
    simp,
    exact hb rfl },
  cases a,
  { rcases mem_zmod_2 b2 with rfl | rfl;
    rcases mem_zmod_2 a2 with rfl | rfl;
    -- while this looks like a non-terminal `simp`, it (almost) isn't: there is only one goal where
    -- it does not finish the proof and on that goal it asks to prove `false`
    simp,
    exact ha rfl },
  { simp [mul_ne_zero _ _, nat.succ_ne_zero _] }
end

instance has_add_L : has_add L :=
{ add := λ ⟨a, ha⟩ ⟨b, hb⟩, ⟨a + b, add_L ha hb⟩ }

instance : has_mul L :=
{ mul := λ ⟨a, ha⟩ ⟨b, hb⟩, ⟨a * b, mul_L ha hb⟩ }

instance : ordered_comm_semiring L :=
begin
  refine function.injective.ordered_comm_semiring _ subtype.coe_injective rfl rfl _ _;
  { refine λ x y, _,
    cases x,
    cases y,
    refl }
end

lemma bot_le : ∀ (a : L), 0 ≤ a :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩,
  cases an,
  { rcases mem_zmod_2 a2 with (rfl | rfl),
    { refl, },
    { exact (ha rfl).elim } },
  { refine or.inr _,
    exact nat.succ_pos _ }
end

instance order_bot : order_bot L :=
{ bot := 0,
  bot_le := bot_le,
  ..(infer_instance : partial_order L) }

lemma lt_of_add_lt_add_left : ∀ (a b c : L), a + b < a + c → b < c :=
λ (a : L) {b c : L}, (add_lt_add_iff_left a).mp

lemma le_iff_exists_add : ∀ (a b : L), a ≤ b ↔ ∃ (c : L), b = a + c :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩ ⟨⟨bn, b2⟩, hb⟩,
  rw subtype.mk_le_mk,
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨rfl, rfl⟩ | h,
    { exact ⟨(0 : L), (add_zero _).symm⟩ },
    { refine ⟨⟨⟨bn - an, b2 + a2⟩, _⟩, _⟩,
      { rw [ne.def, prod.mk.inj_iff, not_and_distrib],
        exact or.inl (ne_of_gt (nat.sub_pos_of_lt h)) },
      { congr,
        { exact (nat.add_sub_cancel' h.le).symm },
        { change b2 = a2 + (b2 + a2),
          rw [add_comm b2, ← add_assoc, add_self_zmod_2, zero_add] } } } },
  { rcases h with ⟨⟨⟨c, c2⟩, hc⟩, abc⟩,
    injection abc with abc,
    rw [prod.mk_add_mk, prod.mk.inj_iff] at abc,
    rcases abc with ⟨rfl, rfl⟩,
    cases c,
    { refine or.inl _,
      rw [ne.def, prod.mk.inj_iff, eq_self_iff_true, true_and] at hc,
      rcases mem_zmod_2 c2 with rfl | rfl,
      { rw [add_zero, add_zero] },
      { exact (hc rfl).elim } },
    { refine or.inr _,
      exact (lt_add_iff_pos_right _).mpr c.succ_pos } }
end

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (a b : L), a * b = 0 → a = 0 ∨ b = 0 :=
begin
  rintros ⟨⟨a, a2⟩, ha⟩ ⟨⟨b, b2⟩, hb⟩ ab1,
  injection ab1 with ab,
  injection ab with abn ab2,
  rw mul_eq_zero at abn,
  rcases abn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { refine or.inl _,
    rcases mem_zmod_2 a2 with rfl | rfl,
    { refl },
    { exact (ha rfl).elim } },
  { refine or.inr _,
    rcases mem_zmod_2 b2 with rfl | rfl,
    { refl },
    { exact (hb rfl).elim } }
end

instance can : canonically_ordered_comm_semiring L :=
{ lt_of_add_lt_add_left := lt_of_add_lt_add_left,
  le_iff_exists_add := le_iff_exists_add,
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  ..(infer_instance : order_bot L),
  ..(infer_instance : ordered_comm_semiring L) }

/--
The elements `(1,0)` and `(1,1)` of `L` are different, but their doubles coincide.
-/
example : ∃ a b : L, a ≠ b ∧ 2 * a = 2 * b :=
begin
  refine ⟨⟨(1,0), by simp⟩, 1, λ (h : (⟨(1, 0), _⟩ : L) = ⟨⟨1, 1⟩, _⟩), _, rfl⟩,
  obtain (F : (0 : zmod 2) = 1) := congr_arg (λ j : L, j.1.2) h,
  cases F,
end

end ex_L
