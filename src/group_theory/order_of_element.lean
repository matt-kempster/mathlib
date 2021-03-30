/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
import algebra.big_operators.order
import group_theory.coset
import data.nat.totient
import data.int.gcd
import data.set.finite

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`g ∈ G` is the minimal `n ≥ 1` such that `g ^ n = 1`.

## Main definitions

* `order_of` defines the order of an element `a` of a group `G`, by convention its value is `0` if
  `a` has infinite order.
* `is_cyclic` is a predicate on a group stating that the group is cyclic.

## Main statements

* `is_cyclic_of_prime_card` proves that a finite group of prime order is cyclic.
* `is_simple_group_of_prime_card`, `is_simple_group.is_cyclic`,
  and `is_simple_group.prime_card` classify finite simple abelian groups.

## Implementation details

Both `order_of` and `is_cyclic` are currently only available for multiplicatively written monoids,
resp. groups.

## Tags

order of an element, cyclic group

## TODO

* Move the first declarations until the definition of order to other files.
* Add the attribute `@[to_additive]` to the declarations in that file so that they also work with
  additive groups.
-/

open function
open_locale big_operators

universe u

variables {α : Type u} {s : set α} {a a₁ a₂ b c: α}

-- TODO mem_range_iff_mem_finset_range_of_mod_eq should be moved elsewhere.
namespace finset
open finset

lemma mem_range_iff_mem_finset_range_of_mod_eq' [decidable_eq α] {f : ℕ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
begin
  split,
  { rintros ⟨i, hi⟩,
    simp only [mem_image, exists_prop, mem_range],
    exact ⟨i % n, nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩ },
  { rintro h,
    simp only [mem_image, exists_prop, set.mem_range, mem_range] at *,
    rcases h with ⟨i, hi, ha⟩,
    use ⟨i, ha⟩ },
end

lemma mem_range_iff_mem_finset_range_of_mod_eq [decidable_eq α] {f : ℤ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
suffices (∃i, f (i % n) = a) ↔ ∃i, i < n ∧ f ↑i = a, by simpa [h],
have hn' : 0 < (n : ℤ), from int.coe_nat_lt.mpr hn,
iff.intro
  (assume ⟨i, hi⟩,
    have 0 ≤ i % ↑n, from int.mod_nonneg _ (ne_of_gt hn'),
    ⟨int.to_nat (i % n),
      by rw [←int.coe_nat_lt, int.to_nat_of_nonneg this]; exact ⟨int.mod_lt_of_pos i hn', hi⟩⟩)
  (assume ⟨i, hi, ha⟩,
    ⟨i, by rw [int.mod_eq_of_lt (int.coe_zero_le _) (int.coe_nat_lt_coe_nat_of_lt hi), ha]⟩)

end finset

lemma mem_normalizer_fintype [group α] {s : set α} [fintype s] {x : α}
  (h : ∀ n, n ∈ s → x * n * x⁻¹ ∈ s) : x ∈ subgroup.set_normalizer s :=
by haveI := classical.prop_decidable;
haveI := set.fintype_image s (λ n, x * n * x⁻¹); exact
λ n, ⟨h n, λ h₁,
have heq : (λ n, x * n * x⁻¹) '' s = s := set.eq_of_subset_of_card_le
  (λ n ⟨y, hy⟩, hy.2 ▸ h y hy.1) (by rw set.card_image_of_injective s conj_injective),
have x * n * x⁻¹ ∈ (λ n, x * n * x⁻¹) '' s := heq.symm ▸ h₁,
let ⟨y, hy⟩ := this in conj_injective hy.2 ▸ hy.1⟩

section order_of
variable [group α]
open quotient_group set

instance fintype_bot : fintype (⊥ : subgroup α) := ⟨{1},
by {rintro ⟨x, ⟨hx⟩⟩, exact finset.mem_singleton_self _}⟩

@[simp] lemma card_trivial :
  fintype.card (⊥ : subgroup α) = 1 :=
fintype.card_eq_one_iff.2
  ⟨⟨(1 : α), set.mem_singleton 1⟩, λ ⟨y, hy⟩, subtype.eq $ subgroup.mem_bot.1 hy⟩

variables [fintype α] [dec : decidable_eq α]

lemma card_eq_card_quotient_mul_card_subgroup (s : subgroup α) [fintype s]
  [decidable_pred (λ a, a ∈ s)] : fintype.card α = fintype.card (quotient s) * fintype.card s :=
by rw ← fintype.card_prod;
  exact fintype.card_congr (subgroup.group_equiv_quotient_times_subgroup)

lemma card_subgroup_dvd_card (s : subgroup α) [fintype s] :
  fintype.card s ∣ fintype.card α :=
by haveI := classical.prop_decidable; simp [card_eq_card_quotient_mul_card_subgroup s]

lemma card_quotient_dvd_card (s : subgroup α) [decidable_pred (λ a, a ∈ s)] [fintype s] :
  fintype.card (quotient s) ∣ fintype.card α :=
by simp [card_eq_card_quotient_mul_card_subgroup s]

end order_of

section order_of

section monoid
variables {α} [monoid α]

open_locale classical

/-- `order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `a ^ n = 1` if it exists.
Otherwise, i.e. if `a` is of infinite order, then `order_of a` is `0` by convention.-/
noncomputable def order_of (a : α) : ℕ :=
if h : ∃ n, 0 < n ∧ a ^ n = 1 then nat.find h else 0

lemma order_of_pos' {a : α} (h : ∃ n, 0 < n ∧ a ^ n = 1) : 0 < order_of a :=
begin
  rw order_of,
  split_ifs,
  exact (nat.find_spec h).1
end

lemma pow_order_of_eq_one (a : α): a ^ order_of a = 1 :=
begin
  rw order_of,
  split_ifs with hfin,
  { exact (nat.find_spec hfin).2 },
  { exact pow_zero a }
end

lemma order_of_eq_zero {a : α} (h : ∀n, 0 < n → a ^ n ≠ 1) : order_of a = 0 :=
begin
  rw order_of,
  split_ifs with hx,
  { exfalso,
    cases hx with n hn,
    exact (h n) hn.1 hn.2 },
  { refl }
end

lemma order_of_le_of_pow_eq_one' {m : ℕ} (h : m < order_of a) : ¬ (0 < m ∧ a ^ m = 1) :=
begin
  rw order_of at h,
  split_ifs at h with hfin,
  { exact nat.find_min hfin h },
  { exfalso, exact nat.not_lt_zero m h }
end

lemma order_of_le_of_pow_eq_one {n : ℕ} (hn : 0 < n) (h : a ^ n = 1) : order_of a ≤ n :=
begin
  by_contradiction h',
  exact (order_of_le_of_pow_eq_one' (not_le.mp h')) ⟨hn, h⟩
end

@[simp] lemma order_of_one : order_of (1 : α) = 1 :=
begin
apply le_antisymm,
{ exact order_of_le_of_pow_eq_one (nat.one_pos) (pow_one 1) },
{ exact nat.succ_le_of_lt ( order_of_pos' ⟨1, ⟨nat.one_pos, pow_one 1⟩⟩) }
end

@[simp] lemma order_of_eq_one_iff : order_of a = 1 ↔ a = 1 :=
⟨λ h, by conv_lhs { rw [← pow_one a, ← h, pow_order_of_eq_one] }, λ h, by simp [h]⟩

lemma pow_eq_mod_order_of {n : ℕ} : a ^ n = a ^ (n % order_of a) :=
calc a ^ n = a ^ (n % order_of a + order_of a * (n / order_of a)) : by rw [nat.mod_add_div]
       ... = a ^ (n % order_of a) : by simp [pow_add, pow_mul, pow_order_of_eq_one]

lemma order_of_dvd_of_pow_eq_one {n : ℕ} (h : a ^ n = 1) : order_of a ∣ n :=
begin
  by_cases h₁ : 0 < n,
  { apply nat.dvd_of_mod_eq_zero,
    by_contradiction h₂,
    have h₃ : ¬ (0 < n % order_of a ∧ a ^ (n % order_of a) = 1) := order_of_le_of_pow_eq_one'
      ( nat.mod_lt _ ( order_of_pos' ⟨n, h₁, h⟩)),
    push_neg at h₃,
    have h₄ : n % order_of a > 0 :=
        nat.pos_of_ne_zero h₂,
    specialize h₃ h₄,
    rw ← pow_eq_mod_order_of at h₃,
    exact h₃ h },
  { have h₅ : n = 0 :=
      le_antisymm (not_lt.mp h₁) (nat.zero_le n),
    simp [h₅] }
end

lemma order_of_dvd_iff_pow_eq_one {n : ℕ} : order_of a ∣ n ↔ a ^ n = 1 :=
⟨λ h, by rw [pow_eq_mod_order_of, nat.mod_eq_zero_of_dvd h, pow_zero], order_of_dvd_of_pow_eq_one⟩

lemma order_of_eq_prime {p : ℕ} [hp : fact p.prime]
  (hg : a^p = 1) (hg1 : a ≠ 1) : order_of a = p :=
(hp.out.2 _ (order_of_dvd_of_pow_eq_one hg)).resolve_left (mt order_of_eq_one_iff.1 hg1)

lemma order_of_eq_order_of_iff {β : Type*} [monoid β] {b : β} :
  order_of a = order_of b ↔ ∀ n : ℕ, a ^ n = 1 ↔ b ^ n = 1 :=
begin
  simp_rw ← order_of_dvd_iff_pow_eq_one,
  exact ⟨λ h n, by rw h, λ h, nat.dvd_antisymm ((h _).mpr (dvd_refl _)) ((h _).mp (dvd_refl _))⟩,
end

lemma order_of_injective {G H : Type*} [monoid G] [monoid H] (f : G →* H)
  (hf : function.injective f) (σ : G) : order_of (f σ) = order_of σ :=
by simp_rw [order_of_eq_order_of_iff, ←f.map_pow, ←f.map_one, hf.eq_iff, iff_self, forall_const]

@[simp, norm_cast] lemma order_of_submonoid {G : Type*} [monoid G] {H : submonoid G} (σ : H) :
  order_of (σ : G) = order_of σ :=
order_of_injective H.subtype subtype.coe_injective σ

@[simp, norm_cast] lemma order_of_subgroup {G : Type*} [group G] {H : subgroup G} (σ : H) :
  order_of (σ : G) = order_of σ :=
order_of_injective H.subtype subtype.coe_injective σ

open nat

-- An example on how to determine the order of an element of a finite group.
example : order_of (-1 : units ℤ) = 2 :=
begin
  haveI : fact (prime 2) := ⟨prime_two⟩,
  exact order_of_eq_prime (by { rw pow_two, simp }) (dec_trivial)
end

lemma order_of_eq_prime_pow {a : α} {p k : ℕ} (hprime : nat.prime p)
  (hnot : ¬ a ^ p ^ k = 1) (hfin : a ^ p ^ (k + 1) = 1) : order_of a = p ^ (k + 1) :=
begin
  apply nat.eq_prime_pow_of_dvd_least_prime_pow hprime;
  { rwa order_of_dvd_iff_pow_eq_one }
end

variables (a) {n : ℕ}

lemma order_of_pow' (h : n ≠ 0) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
begin
  apply dvd_antisymm,
  { apply order_of_dvd_of_pow_eq_one,
    rw [← pow_mul, ← nat.mul_div_assoc _ (gcd_dvd_left _ _), mul_comm,
        nat.mul_div_assoc _ (gcd_dvd_right _ _), pow_mul, pow_order_of_eq_one, one_pow] },
  { have gcd_pos : 0 < gcd (order_of a) n, exact gcd_pos_of_pos_right _ (nat.pos_of_ne_zero h),
    apply coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd gcd_pos),
    apply dvd_of_mul_dvd_mul_right gcd_pos,
    rw [nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc, nat.div_mul_cancel (gcd_dvd_right _ _),
    mul_comm],
    apply order_of_dvd_of_pow_eq_one,
    rw [pow_mul, pow_order_of_eq_one] }
end

variable (n)

lemma order_of_pow'' (h : ∃ n, 0 < n ∧ a ^ n = 1) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
begin
  apply dvd_antisymm,
  { apply order_of_dvd_of_pow_eq_one,
    rw [← pow_mul, ← nat.mul_div_assoc _ (gcd_dvd_left _ _), mul_comm,
        nat.mul_div_assoc _ (gcd_dvd_right _ _), pow_mul, pow_order_of_eq_one, one_pow] },
  { have gcd_pos : 0 < gcd (order_of a) n, from gcd_pos_of_pos_left n (order_of_pos' h),
    apply coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd gcd_pos),
    apply dvd_of_mul_dvd_mul_right gcd_pos,
    rw [nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc,
            nat.div_mul_cancel (gcd_dvd_right _ _), mul_comm],
    apply order_of_dvd_of_pow_eq_one,
    rw [pow_mul, pow_order_of_eq_one] }
end

end monoid

section cancel_monoid
variables {α} [left_cancel_monoid α] (a)

private lemma pow_injective_aux {n m : ℕ} (h : n ≤ m)
  (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
by_contradiction $ assume ne : n ≠ m,
  have h₁ : m - n > 0, from nat.pos_of_ne_zero (by simp [nat.sub_eq_iff_eq_add h, ne.symm]),
  have h₃ : m = n + (m - n), begin exact (nat.add_sub_of_le h).symm end,
  have h₂ : a ^ (m - n) = 1,
    by { rw [h₃, pow_add] at eq, apply mul_left_cancel, convert eq.symm, exact mul_one (a ^ n) },
  have le : order_of a ≤ m - n, from order_of_le_of_pow_eq_one h₁ h₂,
  have lt : m - n < order_of a,
    from (nat.sub_lt_left_iff_lt_add h).mpr $ nat.lt_add_left _ _ _ hm,
  lt_irrefl _ (lt_of_le_of_lt le lt)

lemma pow_injective_of_lt_order_of {n m : ℕ}
  (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
(le_total n m).elim
  (assume h, pow_injective_aux a h hn hm eq)
  (assume h, (pow_injective_aux a h hm hn eq.symm).symm)

end cancel_monoid

section group
variables {α} [group α] {a}

lemma gpow_eq_mod_order_of {i : ℤ} : a ^ i = a ^ (i % order_of a) :=
calc a ^ i = a ^ (i % order_of a + order_of a * (i / order_of a)) :
    by rw [int.mod_add_div]
  ... = a ^ (i % order_of a) :
    by simp [gpow_add, gpow_mul, pow_order_of_eq_one]

end group

section finite_monoid
variables {α} [fintype α] [monoid α]

lemma sum_card_order_of_eq_card_pow_eq_one [decidable_eq α] {n : ℕ} (hn : 0 < n) :
  ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ a : α, order_of a = m)).card
  = (finset.univ.filter (λ a : α, a ^ n = 1)).card :=
calc ∑ m in (finset.range n.succ).filter (∣ n), (finset.univ.filter (λ a : α, order_of a = m)).card
    = _ : (finset.card_bUnion (by { intros, apply finset.disjoint_filter.2, cc })).symm
... = _ : congr_arg finset.card (finset.ext (begin
  assume a,
  suffices : order_of a ≤ n ∧ order_of a ∣ n ↔ a ^ n = 1,
  { simpa [nat.lt_succ_iff], },
  exact ⟨λ h, let ⟨m, hm⟩ := h.2 in by rw [hm, pow_mul, pow_order_of_eq_one, one_pow],
    λ h, ⟨order_of_le_of_pow_eq_one hn h, order_of_dvd_of_pow_eq_one h⟩⟩
end))

end finite_monoid

section finite_cancel_monoid
/-- TODO: Of course everything also works for right_cancel_monoids. -/
variables {α} [fintype α] [left_cancel_monoid α]

/-- TODO: Use this to show that a finite left cancellative monoid is a group.-/
lemma exists_pow_eq_one (a : α) : ∃i, 0 < i ∧ a ^ i = 1 :=
begin
  have h :  ¬ injective (λi:ℕ, a^i),
    from not_injective_infinite_fintype _,
  have h' : ∃(i j : ℕ), a ^ i = a ^ j ∧ i ≠ j,
  { rw injective at h,
    simp only [not_forall, exists_prop] at h,
    exact h },
  rcases h' with ⟨i, j, a_eq, ne⟩,
  wlog h'' : j ≤ i,
  have h''' : a ^ (i - j) = 1,
  { rw [(nat.add_sub_of_le h'').symm, pow_add, ← mul_one (a ^ j), mul_assoc] at a_eq,
    convert mul_left_cancel a_eq,
    rw one_mul },
  use (i - j),
  split,
  { apply lt_of_le_of_ne (zero_le (i - j)),
    by_contradiction,
    rw not_not at h,
    apply ne,
    rw [(nat.add_sub_of_le h'').symm, ← h, add_zero] },
  { exact h''' },
end

lemma order_of_le_card_univ {a : α}: order_of a ≤ fintype.card α :=
finset.le_card_of_inj_on_range ((^) a)
  (assume n _, finset.mem_univ _)
  (assume i hi j hj, pow_injective_of_lt_order_of a hi hj)

/-- This is the same as `order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative monoid.-/
lemma order_of_pos (a : α) : 0 < order_of a :=
begin
  apply order_of_pos',
  cases exists_pow_eq_one a with w hw,
  cases hw with hw1 hw2,
  exact ⟨w, hw1, hw2⟩,
end

variables {n : ℕ}

open nat

lemma exists_pow_eq_self_of_coprime {α : Type*} [monoid α] {a : α} (h : coprime n (order_of a)) :
  ∃ m : ℕ, (a ^ n) ^ m = a :=
begin
  by_cases h0 : order_of a = 0,
  { rw [h0, coprime_zero_right] at h,
    exact ⟨1, by rw [h, pow_one, pow_one]⟩ },
  by_cases h1 : order_of a = 1,
  { rw order_of_eq_one_iff at h1,
    exact ⟨37, by rw [h1, one_pow, one_pow]⟩ },
  obtain ⟨m, hm⟩ :=
    exists_mul_mod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩),
  exact ⟨m, by rw [←pow_mul, pow_eq_mod_order_of, hm, pow_one]⟩,
end

/-- This is the same as `order_of_pow'` and `order_of_pow''` but with one assumption less which is
automatic in the case of a finite cancellative group.-/
lemma order_of_pow (a : α) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
begin
  apply order_of_pow'',
  cases exists_pow_eq_one a with w hw,
  cases hw with hw1 hw2,
  exact ⟨w, hw1, hw2⟩
end

lemma mem_powers_iff_mem_range_order_of [decidable_eq α] {a a' : α} :
  a' ∈ submonoid.powers a ↔ a' ∈ (finset.range (order_of a)).image ((^) a : ℕ → α) :=
finset.mem_range_iff_mem_finset_range_of_mod_eq' (order_of_pos a)
  (assume i, pow_eq_mod_order_of.symm)

noncomputable instance decidable_powers [decidable_eq α] :
  decidable_pred (submonoid.powers a : set α) :=
begin
  assume a',
  apply decidable_of_iff'
    (a' ∈ (finset.range (order_of a)).image ((^) a)),
  exact mem_powers_iff_mem_range_order_of
end

lemma order_eq_card_powers [decidable_eq α] {a : α} :
order_of a = fintype.card (submonoid.powers a : set α) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨pow a n, ⟨n, rfl⟩⟩ },
  { rintros ⟨_, i, rfl⟩ _,
    exact ⟨i % order_of a, mod_lt i (order_of_pos a), subtype.eq pow_eq_mod_order_of.symm⟩ },
  { intros, exact finset.mem_univ _ },
  { intros i j hi hj eq,
    exact pow_injective_of_lt_order_of a hi hj ( by simpa using eq ) }
end

end finite_cancel_monoid

section finite_group
variables {α} [fintype α] [group α]

lemma exists_gpow_eq_one (a : α) : ∃ i ≠ 0, a ^ (i : ℤ) = 1 :=
begin
  rcases exists_pow_eq_one a with ⟨w, hw1, hw2⟩,
  use w,
  split,
  { exact_mod_cast ne_of_gt hw1 },
  { exact_mod_cast hw2 }
end

open subgroup

lemma mem_powers_iff_mem_gpowers {a x : α} : x ∈ submonoid.powers a ↔ x ∈ gpowers a :=
⟨λ ⟨n, hn⟩, ⟨n, by simp * at *⟩,
λ ⟨i, hi⟩, ⟨(i % order_of a).nat_abs,
  by rwa [← gpow_coe_nat, int.nat_abs_of_nonneg (int.mod_nonneg _
    (int.coe_nat_ne_zero_iff_pos.2 (order_of_pos a))),
    ← gpow_eq_mod_order_of]⟩⟩

lemma powers_eq_gpowers (a : α) : (submonoid.powers a : set α) = gpowers a :=
set.ext $ λ x, mem_powers_iff_mem_gpowers

lemma mem_gpowers_iff_mem_range_order_of [decidable_eq α] {a a' : α} :
  a' ∈ subgroup.gpowers a ↔ a' ∈ (finset.range (order_of a)).image ((^) a : ℕ → α) :=
begin
  rw ← mem_powers_iff_mem_gpowers,
  exact mem_powers_iff_mem_range_order_of,
end

noncomputable instance decidable_gpowers [decidable_eq α] :
  decidable_pred (subgroup.gpowers a : set α) :=
begin
  rw ← powers_eq_gpowers,
  exact decidable_powers,
end

lemma order_eq_card_gpowers [decidable_eq α] {a : α} :
order_of a = fintype.card (subgroup.gpowers a : set α) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨gpow a n, ⟨n, rfl⟩⟩ },
  { exact assume ⟨_, i, rfl⟩ _,
    have pos: (0:int) < order_of a,
      from int.coe_nat_lt.mpr $ order_of_pos a,
    have 0 ≤ i % (order_of a),
      from int.mod_nonneg _ $ ne_of_gt pos,
    ⟨int.to_nat (i % order_of a),
      by rw [← int.coe_nat_lt, int.to_nat_of_nonneg this];
        exact ⟨int.mod_lt_of_pos _ pos, subtype.eq gpow_eq_mod_order_of.symm⟩⟩ },
  { intros, exact finset.mem_univ _ },
  { exact assume i j hi hj eq, pow_injective_of_lt_order_of a hi hj $ by simpa using eq }
end

open quotient_group subgroup

/- TODO: use cardinal theory, introduce `card : set α → ℕ`, or setup decidability for cosets -/
lemma order_of_dvd_card_univ : order_of a ∣ fintype.card α :=
begin
  classical,
  have ft_prod : fintype (quotient (gpowers a) × (gpowers a)),
    from fintype.of_equiv α group_equiv_quotient_times_subgroup,
  have ft_s : fintype (gpowers a),
    from @fintype.fintype_prod_right _ _ _ ft_prod _,
  have ft_cosets : fintype (quotient (gpowers a)),
    from @fintype.fintype_prod_left _ _ _ ft_prod ⟨⟨1, (gpowers a).one_mem⟩⟩,
  have eq₁ : fintype.card α = @fintype.card _ ft_cosets * @fintype.card _ ft_s,
    from calc fintype.card α = @fintype.card _ ft_prod :
        @fintype.card_congr _ _ _ ft_prod group_equiv_quotient_times_subgroup
      ... = @fintype.card _ (@prod.fintype _ _ ft_cosets ft_s) :
        congr_arg (@fintype.card _) $ subsingleton.elim _ _
      ... = @fintype.card _ ft_cosets * @fintype.card _ ft_s :
        @fintype.card_prod _ _ ft_cosets ft_s,
  have eq₂ : order_of a = @fintype.card _ ft_s,
    from calc order_of a = _ : order_eq_card_gpowers
      ... = _ : congr_arg (@fintype.card _) $ subsingleton.elim _ _,
  exact dvd.intro (@fintype.card (quotient (subgroup.gpowers a)) ft_cosets)
          (by rw [eq₁, eq₂, mul_comm])
end

@[simp] lemma pow_card_eq_one {a : α} : a ^ fintype.card α = 1 :=
let ⟨m, hm⟩ := @order_of_dvd_card_univ _ a _ _ in
by simp [hm, pow_mul, pow_order_of_eq_one]


variable (a)

/-- TODO: Generalise to `submonoid.powers`.-/
lemma image_range_order_of [decidable_eq α] :
  finset.image (λ i, a ^ i) (finset.range (order_of a)) = (gpowers a : set α).to_finset :=
by { ext x, rw [set.mem_to_finset, set_like.mem_coe, mem_gpowers_iff_mem_range_order_of] }

open nat

/-- TODO: Generalise to `finite_cancel_monoid`. -/
lemma pow_gcd_card_eq_one_iff {n : ℕ} :
  a ^ n = 1 ↔ a ^ (gcd n (fintype.card α)) = 1 :=
⟨λ h, pow_gcd_eq_one _ h $ pow_card_eq_one,
  λ h, let ⟨m, hm⟩ := gcd_dvd_left n (fintype.card α) in
    by rw [hm, pow_mul, h, one_pow]⟩

end finite_group

end order_of

section cyclic


local attribute [instance] set_fintype

open subgroup

/-- A group is called *cyclic* if it is generated by a single element. -/
class is_cyclic (α : Type u) [group α] : Prop :=
(exists_generator [] : ∃ g : α, ∀ x, x ∈ gpowers g)

@[priority 100]
instance is_cyclic_of_subsingleton [group α] [subsingleton α] : is_cyclic α :=
⟨⟨1, λ x, by { rw subsingleton.elim x 1, exact mem_gpowers 1 }⟩⟩

/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `comm_group`. -/
def is_cyclic.comm_group [hg : group α] [is_cyclic α] : comm_group α :=
{ mul_comm := λ x y, show x * y = y * x,
    from let ⟨g, hg⟩ := is_cyclic.exists_generator α in
    let ⟨n, hn⟩ := hg x in let ⟨m, hm⟩ := hg y in
    hm ▸ hn ▸ gpow_mul_comm _ _ _,
  ..hg }

variables [group α]

lemma monoid_hom.map_cyclic {G : Type*} [group G] [h : is_cyclic G] (σ : G →* G) :
  ∃ m : ℤ, ∀ g : G, σ g = g ^ m :=
begin
  obtain ⟨h, hG⟩ := is_cyclic.exists_generator G,
  obtain ⟨m, hm⟩ := hG (σ h),
  use m,
  intro g,
  obtain ⟨n, rfl⟩ := hG g,
  rw [monoid_hom.map_gpow, ←hm, ←gpow_mul, ←gpow_mul'],
end

lemma is_cyclic_of_order_of_eq_card [fintype α]  (x : α)
   (hx : order_of x = fintype.card α) : is_cyclic α :=
begin
  classical,
  use x,
  simp_rw ← set_like.mem_coe,
  rw ← set.eq_univ_iff_forall,
  apply set.eq_of_subset_of_card_le (set.subset_univ _),
  rw [fintype.card_congr (equiv.set.univ α), ← hx, order_eq_card_gpowers],
end

/-- A finite group of prime order is cyclic. -/
lemma is_cyclic_of_prime_card {α : Type u} [group α] [fintype α] {p : ℕ} [hp : fact p.prime]
  (h : fintype.card α = p) : is_cyclic α :=
⟨begin
  obtain ⟨g, hg⟩ : ∃ g : α, g ≠ 1,
  from fintype.exists_ne_of_one_lt_card (by { rw h, exact hp.1.one_lt }) 1,
  classical, -- for fintype (subgroup.gpowers g)
  have : fintype.card (subgroup.gpowers g) ∣ p,
  { rw ←h,
    apply card_subgroup_dvd_card },
  rw nat.dvd_prime hp.1 at this,
  cases this,
  { rw fintype.card_eq_one_iff at this,
    cases this with t ht,
    suffices : g = 1,
    { contradiction },
    have hgt := ht ⟨g, by { change g ∈ subgroup.gpowers g, exact subgroup.mem_gpowers g }⟩,
    rw [←ht 1] at hgt,
    change (⟨_, _⟩ : subgroup.gpowers g) = ⟨_, _⟩ at hgt,
    simpa using hgt },
  { use g,
    intro x,
    rw [←h] at this,
    rw subgroup.eq_top_of_card_eq _ this,
    exact subgroup.mem_top _ }
end⟩

lemma order_of_eq_card_of_forall_mem_gpowers [fintype α]
  {g : α} (hx : ∀ x, x ∈ gpowers g) : order_of g = fintype.card α :=
by { classical, rw [← fintype.card_congr (equiv.set.univ α), order_eq_card_gpowers],
  simp [hx], apply fintype.card_of_finset', simp, intro x, exact hx x}

instance bot.is_cyclic {α : Type u} [group α] : is_cyclic (⊥ : subgroup α) :=
⟨⟨1, λ x, ⟨0, subtype.eq $ eq.symm (subgroup.mem_bot.1 x.2)⟩⟩⟩

instance subgroup.is_cyclic {α : Type u} [group α] [is_cyclic α] (H : subgroup α) : is_cyclic H :=
by haveI := classical.prop_decidable; exact
let ⟨g, hg⟩ := is_cyclic.exists_generator α in
if hx : ∃ (x : α), x ∈ H ∧ x ≠ (1 : α) then
  let ⟨x, hx₁, hx₂⟩ := hx in
  let ⟨k, hk⟩ := hg x in
  have hex : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H,
    from ⟨k.nat_abs, nat.pos_of_ne_zero
      (λ h, hx₂ $ by rw [← hk, int.eq_zero_of_nat_abs_eq_zero h, gpow_zero]),
        match k, hk with
        | (k : ℕ), hk := by rw [int.nat_abs_of_nat, ← gpow_coe_nat, hk]; exact hx₁
        | -[1+ k], hk := by rw [int.nat_abs_of_neg_succ_of_nat,
          ← subgroup.inv_mem_iff H]; simp * at *
        end⟩,
  ⟨⟨⟨g ^ nat.find hex, (nat.find_spec hex).2⟩,
    λ ⟨x, hx⟩, let ⟨k, hk⟩ := hg x in
      have hk₁ : g ^ ((nat.find hex : ℤ) * (k / nat.find hex)) ∈ gpowers (g ^ nat.find hex),
        from ⟨k / nat.find hex, eq.symm $ gpow_mul _ _ _⟩,
      have hk₂ : g ^ ((nat.find hex : ℤ) * (k / nat.find hex)) ∈ H,
        by rw gpow_mul; exact H.gpow_mem (nat.find_spec hex).2 _,
      have hk₃ : g ^ (k % nat.find hex) ∈ H,
        from (subgroup.mul_mem_cancel_right H hk₂).1 $
          by rw [← gpow_add, int.mod_add_div, hk]; exact hx,
      have hk₄ : k % nat.find hex = (k % nat.find hex).nat_abs,
        by rw int.nat_abs_of_nonneg (int.mod_nonneg _
          (int.coe_nat_ne_zero_iff_pos.2 (nat.find_spec hex).1)),
      have hk₅ : g ^ (k % nat.find hex ).nat_abs ∈ H,
        by rwa [← gpow_coe_nat, ← hk₄],
      have hk₆ : (k % (nat.find hex : ℤ)).nat_abs = 0,
        from by_contradiction (λ h,
          nat.find_min hex (int.coe_nat_lt.1 $ by rw [← hk₄];
            exact int.mod_lt_of_pos _ (int.coe_nat_pos.2 (nat.find_spec hex).1))
          ⟨nat.pos_of_ne_zero h, hk₅⟩),
      ⟨k / (nat.find hex : ℤ), subtype.ext_iff_val.2 begin
        suffices : g ^ ((nat.find hex : ℤ) * (k / nat.find hex)) = x,
        { simpa [gpow_mul] },
        rw [int.mul_div_cancel' (int.dvd_of_mod_eq_zero (int.eq_zero_of_nat_abs_eq_zero hk₆)), hk]
      end⟩⟩⟩
else
  have H = (⊥ : subgroup α), from subgroup.ext $ λ x, ⟨λ h, by simp at *; tauto,
    λ h, by rw [subgroup.mem_bot.1 h]; exact H.one_mem⟩,
  by clear _let_match; substI this; apply_instance

open finset nat

section classical

open_locale classical

lemma is_cyclic.card_pow_eq_one_le [decidable_eq α] [fintype α] [is_cyclic α] {n : ℕ}
  (hn0 : 0 < n) : (univ.filter (λ a : α, a ^ n = 1)).card ≤ n :=
let ⟨g, hg⟩ := is_cyclic.exists_generator α in
calc (univ.filter (λ a : α, a ^ n = 1)).card
  ≤ ((gpowers (g ^ (fintype.card α / (gcd n (fintype.card α))))) : set α).to_finset.card :
  card_le_of_subset (λ x hx, let ⟨m, hm⟩ := show x ∈ submonoid.powers g,
    from mem_powers_iff_mem_gpowers.2 $ hg x in
    set.mem_to_finset.2 ⟨(m / (fintype.card α / (gcd n (fintype.card α))) : ℕ),
      have hgmn : g ^ (m * gcd n (fintype.card α)) = 1,
        by rw [pow_mul, hm, ← pow_gcd_card_eq_one_iff]; exact (mem_filter.1 hx).2,
      begin
        rw [gpow_coe_nat, ← pow_mul, nat.mul_div_cancel_left', hm],
        refine dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left (fintype.card α) hn0) _,
        conv {to_lhs,
          rw [nat.div_mul_cancel (gcd_dvd_right _ _), ← order_of_eq_card_of_forall_mem_gpowers hg]},
        exact order_of_dvd_of_pow_eq_one hgmn
      end⟩)
... ≤ n :
  let ⟨m, hm⟩ := gcd_dvd_right n (fintype.card α) in
  have hm0 : 0 < m, from nat.pos_of_ne_zero
    (λ hm0, (by rw [hm0, mul_zero, fintype.card_eq_zero_iff] at hm; exact hm 1)),
  begin
    rw [← fintype.card_of_finset' _ (λ _, set.mem_to_finset), ← order_eq_card_gpowers,
        order_of_pow g, order_of_eq_card_of_forall_mem_gpowers hg],
    rw [hm] {occs := occurrences.pos [2,3]},
    rw [nat.mul_div_cancel_left _  (gcd_pos_of_pos_left _ hn0), gcd_mul_left_left,
      hm, nat.mul_div_cancel _ hm0],
    exact le_of_dvd hn0 (gcd_dvd_left _ _)
  end

end classical

lemma is_cyclic.exists_monoid_generator [fintype α]
[is_cyclic α] : ∃ x : α, ∀ y : α, y ∈ submonoid.powers x :=
by { simp_rw [mem_powers_iff_mem_gpowers], exact is_cyclic.exists_generator α }

section

variables [decidable_eq α] [fintype α]

lemma is_cyclic.image_range_order_of (ha : ∀ x : α, x ∈ gpowers a) :
  finset.image (λ i, a ^ i) (range (order_of a)) = univ :=
begin
  simp_rw [←set_like.mem_coe] at ha,
  simp only [image_range_order_of, set.eq_univ_iff_forall.mpr ha],
  convert set.to_finset_univ
end

lemma is_cyclic.image_range_card (ha : ∀ x : α, x ∈ gpowers a) :
  finset.image (λ i, a ^ i) (range (fintype.card α)) = univ :=
by rw [← order_of_eq_card_of_forall_mem_gpowers ha, is_cyclic.image_range_order_of ha]

end

section totient

variables [decidable_eq α] [fintype α]
(hn : ∀ n : ℕ, 0 < n → (univ.filter (λ a : α, a ^ n = 1)).card ≤ n)

include hn

lemma card_pow_eq_one_eq_order_of_aux (a : α) :
  (finset.univ.filter (λ b : α, b ^ order_of a = 1)).card = order_of a :=
le_antisymm
  (hn _ (order_of_pos a))
  (calc order_of a = @fintype.card (gpowers a) (id _) : order_eq_card_gpowers
    ... ≤ @fintype.card (↑(univ.filter (λ b : α, b ^ order_of a = 1)) : set α)
    (fintype.of_finset _ (λ _, iff.rfl)) :
      @fintype.card_le_of_injective (gpowers a)
        (↑(univ.filter (λ b : α, b ^ order_of a = 1)) : set α)
        (id _) (id _) (λ b, ⟨b.1, mem_filter.2 ⟨mem_univ _,
          let ⟨i, hi⟩ := b.2 in
          by rw [← hi, ← gpow_coe_nat, ← gpow_mul, mul_comm, gpow_mul, gpow_coe_nat,
            pow_order_of_eq_one, one_gpow]⟩⟩) (λ _ _ h, subtype.eq (subtype.mk.inj h))
    ... = (univ.filter (λ b : α, b ^ order_of a = 1)).card : fintype.card_of_finset _ _)

open_locale nat -- use φ for nat.totient

private lemma card_order_of_eq_totient_aux₁ :
  ∀ {d : ℕ}, d ∣ fintype.card α → 0 < (univ.filter (λ a : α, order_of a = d)).card →
  (univ.filter (λ a : α, order_of a = d)).card = φ d
| 0     := λ hd hd0,
let ⟨a, ha⟩ := card_pos.1 hd0 in absurd (mem_filter.1 ha).2 $ ne_of_gt $ order_of_pos a
| (d+1) := λ hd hd0,
let ⟨a, ha⟩ := card_pos.1 hd0 in
have ha : order_of a = d.succ, from (mem_filter.1 ha).2,
have h : ∑ m in (range d.succ).filter (∣ d.succ),
    (univ.filter (λ a : α, order_of a = m)).card =
    ∑ m in (range d.succ).filter (∣ d.succ), φ m, from
  finset.sum_congr rfl
    (λ m hm, have hmd : m < d.succ, from mem_range.1 (mem_filter.1 hm).1,
      have hm : m ∣ d.succ, from (mem_filter.1 hm).2,
      card_order_of_eq_totient_aux₁ (dvd.trans hm hd) (finset.card_pos.2
        ⟨a ^ (d.succ / m), mem_filter.2 ⟨mem_univ _,
          by { rw [order_of_pow a, ha, gcd_eq_right (div_dvd_of_dvd hm),
                nat.div_div_self hm (succ_pos _)]
                }⟩⟩)),
have hinsert : insert d.succ ((range d.succ).filter (∣ d.succ))
    = (range d.succ.succ).filter (∣ d.succ),
  from (finset.ext $ λ x, ⟨λ h, (mem_insert.1 h).elim (λ h, by simp [h, range_succ])
    (by clear _let_match; simp [range_succ]; tauto),
     by clear _let_match; simp [range_succ] {contextual := tt}; tauto⟩),
have hinsert₁ : d.succ ∉ (range d.succ).filter (∣ d.succ),
  by simp [mem_range, zero_le_one, le_succ],
(add_left_inj (∑ m in (range d.succ).filter (∣ d.succ),
  (univ.filter (λ a : α, order_of a = m)).card)).1
  (calc _ = ∑ m in insert d.succ (filter (∣ d.succ) (range d.succ)),
        (univ.filter (λ a : α, order_of a = m)).card :
    eq.symm (finset.sum_insert (by simp [mem_range, zero_le_one, le_succ]))
  ... = ∑ m in (range d.succ.succ).filter (∣ d.succ),
      (univ.filter (λ a : α, order_of a = m)).card :
    sum_congr hinsert (λ _ _, rfl)
  ... = (univ.filter (λ a : α, a ^ d.succ = 1)).card :
    sum_card_order_of_eq_card_pow_eq_one (succ_pos d)
  ... = ∑ m in (range d.succ.succ).filter (∣ d.succ), φ m :
    ha ▸ (card_pow_eq_one_eq_order_of_aux hn a).symm ▸ (sum_totient _).symm
  ... = _ : by rw [h, ← sum_insert hinsert₁];
      exact finset.sum_congr hinsert.symm (λ _ _, rfl))

lemma card_order_of_eq_totient_aux₂ {d : ℕ} (hd : d ∣ fintype.card α) :
  (univ.filter (λ a : α, order_of a = d)).card = φ d :=
by_contradiction $ λ h,
have h0 : (univ.filter (λ a : α , order_of a = d)).card = 0 :=
  not_not.1 (mt pos_iff_ne_zero.2 (mt (card_order_of_eq_totient_aux₁ hn hd) h)),
let c := fintype.card α in
have hc0 : 0 < c, from fintype.card_pos_iff.2 ⟨1⟩,
lt_irrefl c $
  calc c = (univ.filter (λ a : α, a ^ c = 1)).card :
    congr_arg card $ by simp [finset.ext_iff, c]
  ... = ∑ m in (range c.succ).filter (∣ c),
      (univ.filter (λ a : α, order_of a = m)).card :
    (sum_card_order_of_eq_card_pow_eq_one hc0).symm
  ... = ∑ m in ((range c.succ).filter (∣ c)).erase d,
      (univ.filter (λ a : α, order_of a = m)).card :
    eq.symm (sum_subset (erase_subset _ _) (λ m hm₁ hm₂,
      have m = d, by simp at *; cc,
      by simp [*, finset.ext_iff] at *; exact h0))
  ... ≤ ∑ m in ((range c.succ).filter (∣ c)).erase d, φ m :
    sum_le_sum (λ m hm,
      have hmc : m ∣ c, by simp at hm; tauto,
      (imp_iff_not_or.1 (card_order_of_eq_totient_aux₁ hn hmc)).elim
        (λ h, by simp [nat.le_zero_iff.1 (le_of_not_gt h), nat.zero_le])
        (λ h, by rw h))
  ... < φ d + ∑ m in ((range c.succ).filter (∣ c)).erase d, φ m :
    lt_add_of_pos_left _ (totient_pos (nat.pos_of_ne_zero
      (λ h, pos_iff_ne_zero.1 hc0 (eq_zero_of_zero_dvd $ h ▸ hd))))
  ... = ∑ m in insert d (((range c.succ).filter (∣ c)).erase d), φ m :
    eq.symm (sum_insert (by simp))
  ... = ∑ m in (range c.succ).filter (∣ c), φ m : finset.sum_congr
      (finset.insert_erase (mem_filter.2 ⟨mem_range.2 (lt_succ_of_le (le_of_dvd hc0 hd)), hd⟩))
                           (λ _ _, rfl)
  ... = c : sum_totient _

lemma is_cyclic_of_card_pow_eq_one_le : is_cyclic α :=
have (univ.filter (λ a : α, order_of a = fintype.card α)).nonempty,
from (card_pos.1 $
  by rw [card_order_of_eq_totient_aux₂ hn (dvd_refl _)];
  exact totient_pos (fintype.card_pos_iff.2 ⟨1⟩)),
let ⟨x, hx⟩ := this in
is_cyclic_of_order_of_eq_card x (finset.mem_filter.1 hx).2

end totient

lemma is_cyclic.card_order_of_eq_totient [is_cyclic α] [fintype α]
  {d : ℕ} (hd : d ∣ fintype.card α) : (univ.filter (λ a : α, order_of a = d)).card = totient d :=
begin
  classical,
  apply card_order_of_eq_totient_aux₂ (λ n, is_cyclic.card_pow_eq_one_le) hd
end

/-- A finite group of prime order is simple. -/
lemma is_simple_group_of_prime_card {α : Type u} [group α] [fintype α] {p : ℕ} [hp : fact p.prime]
  (h : fintype.card α = p) : is_simple_group α :=
⟨begin
  have h' := nat.prime.one_lt (fact.out p.prime),
  rw ← h at h',
  haveI := fintype.one_lt_card_iff_nontrivial.1 h',
  apply exists_pair_ne α,
end, λ H Hn, begin
  classical,
  have hcard := card_subgroup_dvd_card H,
  rw [h, dvd_prime (fact.out p.prime)] at hcard,
  refine hcard.imp (λ h1, _) (λ hp, _),
  { haveI := fintype.card_le_one_iff_subsingleton.1 (le_of_eq h1),
    apply eq_bot_of_subsingleton },
  { exact eq_top_of_card_eq _ (hp.trans h.symm) }
end⟩

end cyclic

namespace is_simple_group

section comm_group
variables [comm_group α] [is_simple_group α]

@[priority 100]
instance : is_cyclic α :=
begin
  cases subsingleton_or_nontrivial α with hi hi; haveI := hi,
  { apply is_cyclic_of_subsingleton },
  { obtain ⟨g, hg⟩ := exists_ne (1 : α),
    refine ⟨⟨g, λ x, _⟩⟩,
    cases is_simple_lattice.eq_bot_or_eq_top (subgroup.gpowers g) with hb ht,
    { exfalso,
      apply hg,
      rw [← subgroup.mem_bot, ← hb],
      apply subgroup.mem_gpowers },
    { rw ht,
      apply subgroup.mem_top } }
end

theorem prime_card [fintype α] : (fintype.card α).prime :=
begin
  have h0 : 0 < fintype.card α := fintype.card_pos_iff.2 (by apply_instance),
  obtain ⟨g, hg⟩ := is_cyclic.exists_generator α,
  refine ⟨fintype.one_lt_card_iff_nontrivial.2 infer_instance, λ n hn, _⟩,
  refine (is_simple_lattice.eq_bot_or_eq_top (subgroup.gpowers (g ^ n))).symm.imp _ _,
  { intro h,
    have hgo := order_of_pow g,
    rw [order_of_eq_card_of_forall_mem_gpowers hg, nat.gcd_eq_right_iff_dvd.1 hn,
      order_of_eq_card_of_forall_mem_gpowers, eq_comm,
      nat.div_eq_iff_eq_mul_left (nat.pos_of_dvd_of_pos hn h0) hn] at hgo,
    { exact (mul_left_cancel' (ne_of_gt h0) ((mul_one (fintype.card α)).trans hgo)).symm },
    { intro x,
      rw h,
      exact subgroup.mem_top _ } },
  { intro h,
    apply le_antisymm (nat.le_of_dvd h0 hn),
    rw ← order_of_eq_card_of_forall_mem_gpowers hg,
    apply order_of_le_of_pow_eq_one (nat.pos_of_dvd_of_pos hn h0),
    rw [← subgroup.mem_bot, ← h],
    exact subgroup.mem_gpowers _ }
end

end comm_group

end is_simple_group

theorem comm_group.is_simple_iff_is_cyclic_and_prime_card [fintype α] [comm_group α] :
  is_simple_group α ↔ is_cyclic α ∧ (fintype.card α).prime :=
begin
  split,
  { introI h,
    exact ⟨is_simple_group.is_cyclic, is_simple_group.prime_card⟩ },
  { rintro ⟨hc, hp⟩,
    haveI : fact (fintype.card α).prime := ⟨hp⟩,
    exact is_simple_group_of_prime_card rfl }
end
