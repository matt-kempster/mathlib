/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.basic
import ring_theory.ideal.basic

/-!
# Quotients of non-commutative rings

Unfortunately, ideals have only been developed in the commutative case as `ideal`,
and it's not immediately clear how one should formalise ideals in the non-commutative case.

In this file, we directly define the quotient of a semiring by any relation,
by building a bigger relation that represents the ideal generated by that relation.

We prove the universal properties of the quotient,
and recommend avoiding relying on the actual definition!

Since everything runs in parallel for quotients of `R`-algebras, we do that case at the same time.
-/

universes u₁ u₂ u₃ u₄

variables {R : Type u₁} [semiring R]
variables {S : Type u₂} [comm_semiring S]
variables {A : Type u₃} [semiring A] [algebra S A]

namespace ring_quot

/--
Given an arbitrary relation `r` on a ring, we strengthen it to a relation `rel r`,
such that the equivalence relation generated by `rel r` has `x ~ y` if and only if
`x - y` is in the ideal generated by elements `a - b` such that `r a b`.
-/
inductive rel (r : R → R → Prop) : R → R → Prop
| of ⦃x y : R⦄ (h : r x y) : rel x y
| add_left ⦃a b c⦄ : rel a b → rel (a + c) (b + c)
| mul_left ⦃a b c⦄ : rel a b → rel (a * c) (b * c)
| mul_right ⦃a b c⦄ : rel b c → rel (a * b) (a * c)

theorem rel.add_right {r : R → R → Prop} ⦃a b c : R⦄ (h : rel r b c) : rel r (a + b) (a + c) :=
by { rw [add_comm a b, add_comm a c], exact rel.add_left h }

theorem rel.neg {R : Type u₁} [ring R] {r : R → R → Prop} ⦃a b : R⦄ (h : rel r a b) :
  rel r (-a) (-b) :=
by simp only [neg_eq_neg_one_mul a, neg_eq_neg_one_mul b, rel.mul_right h]

theorem rel.smul {r : A → A → Prop} (k : S) ⦃a b : A⦄ (h : rel r a b) : rel r (k • a) (k • b) :=
by simp only [algebra.smul_def, rel.mul_right h]

end ring_quot

/-- The quotient of a ring by an arbitrary relation. -/
def ring_quot (r : R → R → Prop) := quot (ring_quot.rel r)

namespace ring_quot

instance (r : R → R → Prop) : semiring (ring_quot r) :=
{ add           := quot.map₂ (+) rel.add_right rel.add_left,
  add_assoc     := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, exact congr_arg (quot.mk _) (add_assoc _ _ _), },
  zero          := quot.mk _ 0,
  zero_add      := by { rintros ⟨⟩, exact congr_arg (quot.mk _) (zero_add _), },
  add_zero      := by { rintros ⟨⟩, exact congr_arg (quot.mk _) (add_zero _), },
  zero_mul      := by { rintros ⟨⟩, exact congr_arg (quot.mk _) (zero_mul _), },
  mul_zero      := by { rintros ⟨⟩, exact congr_arg (quot.mk _) (mul_zero _), },
  add_comm      := by { rintros ⟨⟩ ⟨⟩, exact congr_arg (quot.mk _) (add_comm _ _), },
  mul           := quot.map₂ (*) rel.mul_right rel.mul_left,
  mul_assoc     := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, exact congr_arg (quot.mk _) (mul_assoc _ _ _), },
  one           := quot.mk _ 1,
  one_mul       := by { rintros ⟨⟩, exact congr_arg (quot.mk _) (one_mul _), },
  mul_one       := by { rintros ⟨⟩, exact congr_arg (quot.mk _) (mul_one _), },
  left_distrib  := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, exact congr_arg (quot.mk _) (left_distrib _ _ _), },
  right_distrib := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, exact congr_arg (quot.mk _) (right_distrib _ _ _), }, }

instance {R : Type u₁} [ring R] (r : R → R → Prop) : ring (ring_quot r) :=
{ neg           := quot.map (λ a, -a)
    rel.neg,
  add_left_neg  := by { rintros ⟨⟩, exact congr_arg (quot.mk _) (add_left_neg _), },
  .. (ring_quot.semiring r) }

instance {R : Type u₁} [comm_semiring R] (r : R → R → Prop) : comm_semiring (ring_quot r) :=
{ mul_comm := by { rintros ⟨⟩ ⟨⟩, exact congr_arg (quot.mk _) (mul_comm _ _), }
  .. (ring_quot.semiring r) }

instance {R : Type u₁} [comm_ring R] (r : R → R → Prop) : comm_ring (ring_quot r) :=
{ .. (ring_quot.comm_semiring r),
  .. (ring_quot.ring r) }

instance (s : A → A → Prop) : algebra S (ring_quot s) :=
{ smul      := λ r, quot.map ((•) r) (rel.smul r),
  to_fun    := λ r, quot.mk _ (algebra_map S A r),
  map_one'  := congr_arg (quot.mk _) (ring_hom.map_one _),
  map_mul'  := λ r s, congr_arg (quot.mk _) (ring_hom.map_mul _ _ _),
  map_zero' := congr_arg (quot.mk _) (ring_hom.map_zero _),
  map_add'  := λ r s, congr_arg (quot.mk _) (ring_hom.map_add _ _ _),
  commutes' := λ r, by { rintro ⟨a⟩, exact congr_arg (quot.mk _) (algebra.commutes _ _) },
  smul_def' := λ r, by { rintro ⟨a⟩, exact congr_arg (quot.mk _) (algebra.smul_def _ _) }, }

instance (r : R → R → Prop) : inhabited (ring_quot r) := ⟨0⟩

/--
The quotient map from a ring to its quotient, as a homomorphism of rings.
-/
def mk_ring_hom (r : R → R → Prop) : R →+* ring_quot r :=
{ to_fun := quot.mk _,
  map_one'  := rfl,
  map_mul'  := λ a b, rfl,
  map_zero' := rfl,
  map_add'  := λ a b, rfl, }

lemma mk_ring_hom_rel {r : R → R → Prop} {x y : R} (w : r x y) :
  mk_ring_hom r x = mk_ring_hom r y :=
quot.sound (rel.of w)

lemma mk_ring_hom_surjective (r : R → R → Prop) : function.surjective (mk_ring_hom r) :=
by { dsimp [mk_ring_hom], rintro ⟨⟩, simp, }

@[ext]
lemma ring_quot_ext {T : Type u₄} [semiring T] {r : R → R → Prop} (f g : ring_quot r →+* T)
  (w : f.comp (mk_ring_hom r) = g.comp (mk_ring_hom r)) : f = g :=
begin
  ext,
  rcases mk_ring_hom_surjective r x with ⟨x, rfl⟩,
  exact (ring_hom.congr_fun w x : _),
end

variables  {T : Type u₄} [semiring T]

/--
Any ring homomorphism `f : R →+* T` which respects a relation `r : R → R → Prop`
factors uniquely through a morphism `ring_quot r →+* T`.
-/
def lift {r : R → R → Prop} :
  {f : R →+* T // ∀ ⦃x y⦄, r x y → f x = f y} ≃ (ring_quot r →+* T) :=
{ to_fun := λ f', let f := (f' : R →+* T) in
  { to_fun := quot.lift f
    begin
      rintros _ _ r,
      induction r,
      case of : _ _ r { exact f'.prop r, },
      case add_left : _ _ _ _ r' { simp [r'], },
      case mul_left : _ _ _ _ r' { simp [r'], },
      case mul_right : _ _ _ _ r' { simp [r'], },
    end,
    map_zero' := f.map_zero,
    map_add' := by { rintros ⟨x⟩ ⟨y⟩, exact f.map_add x y, },
    map_one' := f.map_one,
    map_mul' := by { rintros ⟨x⟩ ⟨y⟩, exact f.map_mul x y, }, },
  inv_fun := λ F, ⟨F.comp (mk_ring_hom r), λ x y h, by { dsimp, rw mk_ring_hom_rel h, }⟩,
  left_inv := λ f, by { ext, simp, refl },
  right_inv := λ F, by { ext, simp, refl } }

@[simp]
lemma lift_mk_ring_hom_apply (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
  lift ⟨f, w⟩ (mk_ring_hom r x) = f x :=
rfl

-- note this is essentially `lift.symm_apply_eq.mp h`
lemma lift_unique (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y)
  (g : ring_quot r →+* T) (h : g.comp (mk_ring_hom r) = f) : g = lift ⟨f, w⟩ :=
by { ext, simp [h], }

lemma eq_lift_comp_mk_ring_hom {r : R → R → Prop} (f : ring_quot r →+* T) :
  f = lift ⟨f.comp (mk_ring_hom r), λ x y h, by { dsimp, rw mk_ring_hom_rel h, }⟩ :=
(lift.apply_symm_apply f).symm

section comm_ring
/-!
We now verify that in the case of a commutative ring, the `ring_quot` construction
agrees with the quotient by the appropriate ideal.
-/

variables {B : Type u₁} [comm_ring B]

/-- The universal ring homomorphism from `ring_quot r` to `(ideal.of_rel r).quotient`. -/
def ring_quot_to_ideal_quotient (r : B → B → Prop) :
  ring_quot r →+* (ideal.of_rel r).quotient :=
lift
  ⟨ideal.quotient.mk (ideal.of_rel r),
   λ x y h, quot.sound (submodule.mem_Inf.mpr (λ p w, w ⟨x, y, h, sub_add_cancel x y⟩))⟩

@[simp] lemma ring_quot_to_ideal_quotient_apply (r : B → B → Prop) (x : B) :
  ring_quot_to_ideal_quotient r (mk_ring_hom r x) = ideal.quotient.mk _ x := rfl

/-- The universal ring homomorphism from `(ideal.of_rel r).quotient` to `ring_quot r`. -/
def ideal_quotient_to_ring_quot (r : B → B → Prop) :
  (ideal.of_rel r).quotient →+* ring_quot r :=
ideal.quotient.lift (ideal.of_rel r) (mk_ring_hom r)
begin
  refine λ x h, submodule.span_induction h _ _ _ _,
  { rintro y ⟨a, b, h, su⟩,
    symmetry' at su,
    rw ←sub_eq_iff_eq_add at su,
    rw [ ← su, ring_hom.map_sub, mk_ring_hom_rel h, sub_self], },
  { simp, },
  { intros a b ha hb, simp [ha, hb], },
  { intros a x hx, simp [hx], },
end

@[simp] lemma ideal_quotient_to_ring_quot_apply (r : B → B → Prop) (x : B) :
  ideal_quotient_to_ring_quot r (ideal.quotient.mk _ x) = mk_ring_hom r x := rfl

/--
The ring equivalence between `ring_quot r` and `(ideal.of_rel r).quotient`
-/
def ring_quot_equiv_ideal_quotient (r : B → B → Prop) :
  ring_quot r ≃+* (ideal.of_rel r).quotient :=
ring_equiv.of_hom_inv (ring_quot_to_ideal_quotient r) (ideal_quotient_to_ring_quot r)
  (by { ext, simp, }) (by { ext ⟨x⟩, simp, })

end comm_ring

/-- Transfer a star_ring instance through a quotient, if the quotient is invariant to `star` -/
def star_ring {R : Type u₁} [semiring R] [star_ring R] (r : R → R → Prop)
  (hr : ∀ {a b}, r a b → r (star a) (star b)) :
  star_ring (ring_quot r) :=
{ star := quot.map star $ λ a b h, begin
    induction h,
    { exact rel.of (hr h_h) },
    { rw [star_add, star_add], exact rel.add_left h_ih, },
    { rw [star_mul, star_mul], exact rel.mul_right h_ih, },
    { rw [star_mul, star_mul], exact rel.mul_left h_ih, },
  end,
  star_involutive := by { rintros ⟨⟩, exact congr_arg (quot.mk _) (star_star _), },
  star_mul := by { rintros ⟨⟩ ⟨⟩, exact congr_arg (quot.mk _) (star_mul _ _), },
  star_add := by { rintros ⟨⟩ ⟨⟩, exact congr_arg (quot.mk _) (star_add _ _), } }

section algebra

variables (S)

/--
The quotient map from an `S`-algebra to its quotient, as a homomorphism of `S`-algebras.
-/
def mk_alg_hom (s : A → A → Prop) : A →ₐ[S] ring_quot s :=
{ commutes' := λ r, rfl,
  ..mk_ring_hom s }

@[simp]
lemma mk_alg_hom_coe (s : A → A → Prop) : (mk_alg_hom S s : A →+* ring_quot s) = mk_ring_hom s :=
rfl

lemma mk_alg_hom_rel {s : A → A → Prop} {x y : A} (w : s x y) :
  mk_alg_hom S s x = mk_alg_hom S s y :=
quot.sound (rel.of w)

lemma mk_alg_hom_surjective (s : A → A → Prop) : function.surjective (mk_alg_hom S s) :=
by { dsimp [mk_alg_hom], rintro ⟨a⟩, use a, refl, }

variables {B : Type u₄} [semiring B] [algebra S B]

@[ext]
lemma ring_quot_ext' {s : A → A → Prop}
  (f g : ring_quot s →ₐ[S] B) (w : f.comp (mk_alg_hom S s) = g.comp (mk_alg_hom S s)) : f = g :=
begin
  ext,
  rcases mk_alg_hom_surjective S s x with ⟨x, rfl⟩,
  exact (alg_hom.congr_fun w x : _),
end

/--
Any `S`-algebra homomorphism `f : A →ₐ[S] B` which respects a relation `s : A → A → Prop`
factors uniquely through a morphism `ring_quot s →ₐ[S]  B`.
-/
def lift_alg_hom {s : A → A → Prop} :
  { f : A →ₐ[S] B // ∀ ⦃x y⦄, s x y → f x = f y} ≃ (ring_quot s →ₐ[S] B) :=
{ to_fun := λ f', let f := (f' : A →ₐ[S] B) in
  { to_fun := quot.lift f
    begin
      rintros _ _ r,
      induction r,
      case of : _ _ r { exact f'.prop r, },
      case add_left : _ _ _ _ r' { simp [r'], },
      case mul_left : _ _ _ _ r' { simp [r'], },
      case mul_right : _ _ _ _ r' { simp [r'], },
    end,
    map_zero' := f.map_zero,
    map_add' := by { rintros ⟨x⟩ ⟨y⟩, exact f.map_add x y, },
    map_one' := f.map_one,
    map_mul' := by { rintros ⟨x⟩ ⟨y⟩, exact f.map_mul x y, },
    commutes' :=
    begin
      rintros x,
      conv_rhs { rw [algebra.algebra_map_eq_smul_one, ←f.map_one, ←f.map_smul], },
      rw algebra.algebra_map_eq_smul_one,
      exact quot.lift_mk f f'.prop (x • 1),
    end, },
  inv_fun := λ F, ⟨F.comp (mk_alg_hom S s), λ _ _ h, by { dsimp, erw mk_alg_hom_rel S h }⟩,
  left_inv := λ f, by { ext, simp, refl },
  right_inv := λ F, by { ext, simp, refl } }

@[simp]
lemma lift_alg_hom_mk_alg_hom_apply (f : A →ₐ[S] B) {s : A → A → Prop}
  (w : ∀ ⦃x y⦄, s x y → f x = f y) (x) :
  (lift_alg_hom S ⟨f, w⟩) ((mk_alg_hom S s) x) = f x :=
rfl

-- note this is essentially `(lift_alg_hom S).symm_apply_eq.mp h`
lemma lift_alg_hom_unique (f : A →ₐ[S] B) {s : A → A → Prop} (w : ∀ ⦃x y⦄, s x y → f x = f y)
  (g : ring_quot s →ₐ[S] B) (h : g.comp (mk_alg_hom S s) = f) : g = lift_alg_hom S ⟨f, w⟩ :=
by { ext, simp [h], }

lemma eq_lift_alg_hom_comp_mk_alg_hom {s : A → A → Prop} (f : ring_quot s →ₐ[S] B) :
  f = lift_alg_hom S ⟨f.comp (mk_alg_hom S s), λ x y h, by { dsimp, erw mk_alg_hom_rel S h, }⟩ :=
((lift_alg_hom S).apply_symm_apply f).symm

end algebra

attribute [irreducible] mk_ring_hom mk_alg_hom lift lift_alg_hom

end ring_quot
