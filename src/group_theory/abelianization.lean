/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.
-/

import group_theory.quotient_group
import tactic.group

universes u v

-- let G be a group
variables (G : Type u) [group G]

/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹` -/
@[derive subgroup.normal]
def commutator : subgroup G :=
subgroup.normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

def general_commutator (H₁ : subgroup G) (H₂ : subgroup G) : subgroup G :=
subgroup.closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x}

lemma general_commutator_is_normal (H₁ : subgroup G) (H₂ : subgroup G) [subgroup.normal H₁]
  [subgroup.normal H₂] : subgroup.normal (general_commutator G H₁ H₂) :=
begin
  let base : set G := {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x},
  suffices : base = group.conjugates_of_set base,
  { dsimp only [general_commutator, ←base],
    rw this,
    exact subgroup.normal_closure_normal },
  apply set.subset.antisymm group.subset_conjugates_of_set,
  intros a h,
  rw group.mem_conjugates_of_set_iff at h,
  cases h with b ha,
  cases ha with hb ha,
  cases ha with d ha,
  cases hb with c hb,
  cases hb with hc hb,
  cases hb with e hb,
  cases hb with he hb,
  rw [←ha, ←hb],
  exact ⟨d * c * d⁻¹, ⟨_inst_2.conj_mem c hc d, ⟨d * e * d⁻¹, ⟨_inst_3.conj_mem e he d, by group⟩⟩⟩⟩,
end

def nth_commutator (n : ℕ) : subgroup G :=
nat.rec_on n (⊤ : subgroup G) (λ _ H, general_commutator G H H)
-- I've heard it's typically better to give definitions in term mode because it makes
-- them more amenable to refl. I'm not sure it makes a big difference here, but I think
-- what I've written above is a term mode version of the tactic mode definition commented out below
-- begin
--   induction n,
--   exact (⊤ : subgroup G),
--   exact general_commutator G n_ih n_ih,
-- end

--lemma nth_commutator_normal (n:ℕ):(nth_commutator G n).normal:=
--begin
  --induction n,
  --change (⊤:subgroup G).normal,
  --sorry,
  --sorry,
--end

def is_solvable : Prop := ∃ n : ℕ, nth_commutator G n = (⊥ : subgroup G)


lemma commutator_eq_general_commutator_top_top :
  commutator G = general_commutator G (⊤ : subgroup G) (⊤ : subgroup G) := sorry




/-- The abelianization of G is the quotient of G by its commutator subgroup -/
def abelianization : Type u :=
quotient_group.quotient (commutator G)

namespace abelianization

local attribute [instance] quotient_group.left_rel

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b,
  begin
    apply quotient.sound,
    apply subgroup.subset_normal_closure,
    use b⁻¹, use a⁻¹,
    group,
  end,
.. quotient_group.quotient.group _ }

instance : inhabited (abelianization G) := ⟨1⟩

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* abelianization G :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

section lift
-- so far -- built Gᵃᵇ and proved it's an abelian group.
-- defined `of : G → Gᵃᵇ`

-- let A be an abelian group and let f be a group hom from G to A
variables {A : Type v} [comm_group A] (f : G →* A)

lemma commutator_subset_ker : commutator G ≤ f.ker :=
begin
  apply subgroup.normal_closure_le_normal,
  rintros x ⟨p, q, rfl⟩,
  simp [monoid_hom.mem_ker, mul_right_comm (f p) (f q)],
end

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map from
  the abelianization of a `G` to `A` that factors through `f`. -/
def lift : abelianization G →* A :=
quotient_group.lift _ f (λ x h, f.mem_ker.2 $ commutator_subset_ker _ h)

@[simp] lemma lift.of (x : G) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (φ : abelianization G →* A)
  -- hφ : φ agrees with f on the image of G in Gᵃᵇ
  (hφ : ∀ (x : G), φ (of x) = f x)
  {x : abelianization G} :
  φ x = lift f x :=
quotient_group.induction_on x hφ

end lift

variables {A : Type v} [monoid A]

theorem hom_ext (φ ψ : abelianization G →* A)
  (h : φ.comp of = ψ.comp of) : φ = ψ :=
begin
  ext x,
  apply quotient_group.induction_on x,
  intro z,
  show φ.comp of z = _,
  rw h,
  refl,
end

end abelianization
