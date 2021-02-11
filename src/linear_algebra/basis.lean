/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import linear_algebra.linear_independent
import linear_algebra.projection
import linear_algebra.linear_pmap
import data.fintype.card

/-!

# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `basis ι R M` is the type of `ι`-indexed `R`-bases for a semimodule `M`,
  represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.

* `basis.repr` is the isomorphism sending `x : M` and to its coordinates `basis.repr x : ι →₀ R`

* `basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.

## Main statements

* `basis.mk`: a linear independent set of vectors spanning the whole module determines a basis

* `basis.ext` states that two linear maps are equal if they coincide on a basis.

* `nonempty_basis` states that every vector space has a basis.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/

noncomputable theory

universe u

open function set submodule
open_locale classical big_operators

variables {ι : Type*} {ι' : Type*} {R : Type*} {K : Type*}
variables {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

section semimodule

variables [semiring R]
variables [add_comm_monoid M] [semimodule R M] [add_comm_monoid M'] [semimodule R M']

section
variables (ι) (R) (M)

/-- A `basis ι R M` for a semimodule `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `coe_fn (b : basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `basis.repr`.
-/
structure basis := of_repr :: (repr : M ≃ₗ[R] (ι →₀ R))

end

namespace basis

instance : inhabited (basis ι R (ι →₀ R)) := ⟨basis.of_repr (linear_equiv.refl _ _)⟩

variables (b b₁ : basis ι R M) (i : ι) (c : R) (v : ι →₀ R) (x : M)

section repr

/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (basis ι R M) :=
{ F := λ _, ι → M,
  coe := λ b i, b.repr.symm (finsupp.single i 1) }

@[simp] lemma coe_of_repr (e : M ≃ₗ[R] (ι →₀ R)) :
  ⇑(of_repr e) = λ i, e.symm (finsupp.single i 1) :=
rfl

protected lemma injective [nontrivial R] : injective b :=
b.repr.symm.injective.comp (λ _ _, (finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp)

lemma repr_symm_single_one : b.repr.symm (finsupp.single i 1) = b i := rfl

lemma repr_symm_single : b.repr.symm (finsupp.single i c) = c • b i :=
calc b.repr.symm (finsupp.single i c)
    = b.repr.symm (c • finsupp.single i 1) : by rw [finsupp.smul_single', mul_one]
... = c • b i : by rw [linear_equiv.map_smul, repr_symm_single_one]

@[simp] lemma repr_self : b.repr (b i) = finsupp.single i 1 :=
linear_equiv.apply_symm_apply _ _

@[simp] lemma repr_symm_apply (v) : b.repr.symm v = finsupp.total ι M R b v :=
calc b.repr.symm v = b.repr.symm (v.sum finsupp.single) : by simp
... = ∑ i in v.support, b.repr.symm (finsupp.single i (v i)) :
  by rw [finsupp.sum, linear_equiv.map_sum]
... = finsupp.total ι M R b v :
  by simp [repr_symm_single, finsupp.total_apply, finsupp.sum]

@[simp] lemma coe_repr_symm : ↑b.repr.symm = finsupp.total ι M R b :=
linear_map.ext (λ v, b.repr_symm_apply v)

@[simp] lemma repr_total : b.repr (finsupp.total _ _ _ b v) = v :=
by { rw ← b.coe_repr_symm, exact b.repr.apply_symm_apply v }

@[simp] lemma total_repr : finsupp.total _ _ _ b (b.repr x) = x :=
by { rw ← b.coe_repr_symm, exact b.repr.symm_apply_apply x }

end repr

section ext

variables {M₁ : Type*} [add_comm_monoid M₁] [semimodule R M₁]

/-- Two linear maps are equal if they are equal on basis vectors. -/
theorem ext {f₁ f₂ : M →ₗ[R] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
by { ext x,
     rw [← b.total_repr x, finsupp.total_apply, finsupp.sum],
     simp only [linear_map.map_sum, linear_map.map_smul, h] }

/-- Two linear equivs are equal if they are equal on basis vectors. -/
theorem ext' {f₁ f₂ : M ≃ₗ[R] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
by { ext x,
      rw [← b.total_repr x, finsupp.total_apply, finsupp.sum],
      simp only [linear_equiv.map_sum, linear_equiv.map_smul, h] }

lemma repr_eq_iff {b : basis ι R M} {f : M →ₗ[R] ι →₀ R} :
  ↑b.repr = f ↔ ∀ i, f (b i) = finsupp.single i 1 :=
⟨λ h i, h ▸ b.repr_self i,
 λ h, b.ext (λ i, (b.repr_self i).trans (h i).symm)⟩

lemma repr_eq_iff' {b : basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
  b.repr = f ↔ ∀ i, f (b i) = finsupp.single i 1 :=
⟨λ h i, h ▸ b.repr_self i,
  λ h, b.ext' (λ i, (b.repr_self i).trans (h i).symm)⟩

/-- An unbundled version of `repr_eq_iff` -/
lemma repr_apply_eq {f : M → ι → R}
  (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x)
  (f_eq : ∀ i, f (b i) = finsupp.single i 1) (x : M) (i : ι) :
  b.repr x i = f x i :=
begin
  let f_i : M →ₗ[R] R :=
  { to_fun := λ x, f x i,
    map_add' := λ _ _, by rw [hadd, pi.add_apply],
    map_smul' := λ _ _, by rw [hsmul, pi.smul_apply] },
  have : (finsupp.lapply i).comp ↑b.repr = f_i,
  { refine b.ext (λ j, _),
    show b.repr (b j) i = f (b j) i,
    rw [b.repr_self, f_eq] },
  calc b.repr x i = f_i x : by { rw ← this, refl }
              ... = f x i : rfl
end

/-- Two bases are equal if they assign the same coordinates. -/
lemma eq_of_repr_eq_repr {b₁ b₂ : basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) :
  b₁ = b₂ :=
have b₁.repr = b₂.repr, by { ext, apply h },
by { cases b₁, cases b₂, simpa }

/-- Two bases are equal if their basis vectors are the same. -/
@[ext] lemma eq_of_apply_eq {b₁ b₂ : basis ι R M} (h : ∀ i, b₁ i = b₂ i) : b₁ = b₂ :=
suffices b₁.repr = b₂.repr, by { cases b₁, cases b₂, simpa },
repr_eq_iff'.mpr (λ i, by rw [h, b₂.repr_self])

end ext

section reindex

variables (b' : basis ι' R M')
variables (e : ι ≃ ι')

/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
def reindex : basis ι' R M :=
basis.of_repr (b.repr.trans (finsupp.dom_lcongr e))

@[simp] lemma reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
show (b.repr.trans (finsupp.dom_lcongr e)).symm (finsupp.single i' 1) =
  b.repr.symm (finsupp.single (e.symm i') 1),
by rw [linear_equiv.symm_trans_apply, finsupp.dom_lcongr_symm, finsupp.dom_lcongr_single]

@[simp] lemma coe_reindex_repr : ((b.reindex e).repr x : ι' → R) = b.repr x ∘ e.symm :=
funext $ λ i',
show (finsupp.dom_lcongr e : _ ≃ₗ[R] _) (b.repr x) i' = _,
from finsupp.dom_lcongr_apply _ _ _

@[simp] lemma reindex_repr (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
by rw coe_reindex_repr

/-- `b.reindex_range` is a basis indexed by `range b`, the basis vectors themselves. -/
def reindex_range [nontrivial R] : basis (range b) R M :=
b.reindex (equiv.of_injective b b.injective)

@[simp] lemma reindex_range_apply [nontrivial R] {bi : M} {i : ι} (h : b i = bi) :
  b.reindex_range ⟨bi, ⟨i, h⟩⟩ = b i :=
begin
  rw [reindex_range, reindex_apply, equiv.of_injective],
  subst h,
  exact congr_arg _ (equiv.of_bijective_symm_apply_apply _ _ _)
end

@[simp] lemma reindex_range_repr [nontrivial R] (x : M) {bi : M} {i : ι} (h : b i = bi) :
  b.reindex_range.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i :=
begin
  rw [reindex_range, reindex_repr, equiv.of_injective],
  subst h,
  exact congr_arg _ (equiv.of_bijective_symm_apply_apply _ _ _)
end

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
def equiv : M ≃ₗ[R] M' :=
b.repr.trans (b'.reindex e.symm).repr.symm

@[simp] lemma equiv_apply : b.equiv b' e (b i) = b' (e i) :=
by simp [equiv]

@[simp] lemma equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
b'.ext' $ λ i', b.repr.injective $ finsupp.ext $ λ i,
  by { rw [equiv_apply, equiv, linear_equiv.symm_trans_apply, b.repr.apply_symm_apply,
           linear_equiv.symm_symm, reindex_repr, equiv.symm_symm, b.repr_self, b'.repr_self],
     sorry }

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are in bijection,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (f i)`
-/
def equiv' (f : M → M') (g : M' → M)
  (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
  (hgf : ∀i, g (f (v i)) = v i) (hfg : ∀i, f (g (v' i)) = v' i) :
  M ≃ₗ M' :=
{ inv_fun := hv'.constr (g ∘ v'),
  left_inv :=
    have (hv'.constr (g ∘ v')).comp (hv.constr (f ∘ v)) = linear_map.id,
    from hv.ext $ λ i, exists.elim (hf i)
      (λ i' hi', by simp [constr_basis, hi'.symm]; rw [hi', hgf]),
    λ x, congr_arg (λ h:M →ₗ[R] M, h x) this,
  right_inv :=
    have (hv.constr (f ∘ v)).comp (hv'.constr (g ∘ v')) = linear_map.id,
    from hv'.ext $ λ i', exists.elim (hg i')
      (λ i hi, by simp [constr_basis, hi.symm]; rw [hi, hfg]),
    λ y, congr_arg (λ h:M' →ₗ[R] M', h y) this,
  ..hv.constr (f ∘ v) }

@[simp] lemma linear_equiv_of_is_basis_comp {ι'' : Type*} {v : ι → M} {v' : ι' → M'}
  {v'' : ι'' → M''} (hv : is_basis R v) (hv' : is_basis R v') (hv'' : is_basis R v'')
  (e : ι ≃ ι') (f : ι' ≃ ι'' ) :
  (linear_equiv_of_is_basis hv hv' e).trans (linear_equiv_of_is_basis hv' hv'' f) =
  linear_equiv_of_is_basis hv hv'' (e.trans f) :=
begin
  apply linear_equiv.injective_to_linear_map,
  apply hv.ext,
  intros i,
  simp [linear_equiv_of_is_basis]
end

@[simp] lemma linear_equiv_of_is_basis_refl :
  linear_equiv_of_is_basis hv hv (equiv.refl ι) = linear_equiv.refl R M :=
begin
  apply linear_equiv.injective_to_linear_map,
  apply hv.ext,
  intros i,
  simp [linear_equiv_of_is_basis]
end

lemma linear_equiv_of_is_basis_trans_symm (e : ι ≃ ι') {v' : ι' → M'} (hv' : is_basis R v') :
  (linear_equiv_of_is_basis hv hv' e).trans (linear_equiv_of_is_basis hv' hv e.symm) = linear_equiv.refl R M :=
by simp

lemma linear_equiv_of_is_basis_symm_trans (e : ι ≃ ι') {v' : ι' → M'} (hv' : is_basis R v') :
  (linear_equiv_of_is_basis hv' hv e.symm).trans (linear_equiv_of_is_basis hv hv' e) = linear_equiv.refl R M' :=
by simp


end reindex

protected lemma linear_independent : linear_independent R b :=
linear_independent_iff.mpr $ λ l hl,
calc l = b.repr (finsupp.total _ _ _ b l) : (b.repr_total l).symm
   ... = 0 : by rw [hl, linear_equiv.map_zero]

section constr

variables (S : Type*) [semiring S] [semimodule S M] [semimodule S M']
variables [smul_comm_class R S M] [smul_comm_class R S M']

@[simp] lemma finsupp.map_domain_single {α β M : Type*} [add_comm_monoid M]
  (f : α → β) (x : α) (y : M) :
  finsupp.map_domain f (finsupp.single x y) = finsupp.single (f x) y :=
by { ext i, simp [finsupp.map_domain] }

/-- Construct a linear map given the value at the basis.

This definition is parameterized over an extra `semiring S`,
such that `smul_comm_class R S M` and `smul_comm_class R S M'` hold.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `add_equiv` by setting `S := ℕ`.
-/
def constr : (ι → M') ≃ₗ[S] (M →ₗ[R] M') :=
{ to_fun := λ f, (finsupp.total M' M' R id).comp $ (finsupp.lmap_domain R R f).comp b.repr,
  inv_fun := λ f i, f (b i),
  left_inv := λ f, by { ext, simp },
  right_inv := λ f, by { refine b.ext (λ i, _), simp },
  map_add' := λ f g, by { refine b.ext (λ i, _), simp },
  map_smul' := λ c f, by { refine b.ext (λ i, _), simp } }

theorem constr_def (f : ι → M') :
  b.constr S f = (finsupp.total M' M' R id).comp ((finsupp.lmap_domain R R f).comp b.repr) :=
rfl

theorem constr_apply (f : ι → M') (x : M) :
  b.constr S f x = (b.repr x).sum (λ b a, a • f b) :=
by { simp only [constr_def, linear_map.comp_apply, finsupp.lmap_domain_apply, finsupp.total_apply],
     rw finsupp.sum_map_domain_index; simp [add_smul] }

@[simp] lemma constr_basis {f : ι → M'} {i : ι} :
  (b.constr S f : M → M') (b i) = f i :=
by simp [basis.constr_apply, b.repr_self]

lemma constr_eq {g : ι → M'} {f : M →ₗ[R] M'}
  (h : ∀i, g i = f (b i)) : b.constr S g = f :=
b.ext $ λ i, (b.constr_basis S).trans (h i)

lemma constr_self (f : M →ₗ[R] M') : b.constr S (λ i, f (b i)) = f :=
b.constr_eq S $ λ x, rfl

lemma constr_range [nonempty ι] {f : ι  → M'} :
  (b.constr S f).range = span R (range f) :=
by rw [b.constr_def S f, linear_map.range_comp, linear_map.range_comp, linear_equiv.range,
       ← finsupp.supported_univ, finsupp.lmap_domain_supported, ←set.image_univ,
       ← finsupp.span_eq_map_total, set.image_id]

end constr

end basis

end semimodule

section module

open linear_map

variables {v : ι → M}
variables [ring R] [add_comm_group M] [add_comm_group M'] [add_comm_group M'']
variables [module R M] [module R M'] [module R M'']
variables {c d : R} {x y : M}
variables (b : basis ι R M)

namespace basis

section mk

variables (hli : linear_independent R v) (hsp : span R (range v) = ⊤)

/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : basis ι R M :=
basis.of_repr
{ inv_fun := finsupp.total _ _ _ v,
  left_inv := λ x, hli.total_repr ⟨x, _⟩,
  right_inv := λ x, hli.repr_eq rfl,
  .. hli.repr.comp (linear_map.id.cod_restrict _ (λ h, hsp.symm ▸ submodule.mem_top)) }

@[simp] lemma mk_repr :
  (basis.mk hli hsp).repr x = hli.repr ⟨x, hsp.symm ▸ submodule.mem_top⟩ :=
rfl

@[simp] lemma mk_apply (i : ι) : basis.mk hli hsp i = v i :=
show finsupp.total _ _ _ v _ = v i, by simp

@[simp] lemma coe_mk : ⇑(basis.mk hli hsp) = v :=
funext (mk_apply _ _)

end mk

end basis

variables (R) (v)
/-- A family of vectors is a basis if it is linearly independent and all vectors are in the span. -/
def is_basis := linear_independent R v ∧ span R (range v) = ⊤
variables {R} {v}

section is_basis
variables {s t : set M} (hv : is_basis R v)

/-- Canonical equivalence between a module and the linear combinations of basis vectors. -/
def module_equiv_finsupp (hv : is_basis R v) : M ≃ₗ[R] ι →₀ R :=
(hv.1.total_equiv.trans (linear_equiv.of_top _ hv.2)).symm

@[simp] theorem module_equiv_finsupp_apply_basis (hv : is_basis R v) (i : ι) :
  module_equiv_finsupp hv (v i) = finsupp.single i 1 :=
(linear_equiv.symm_apply_eq _).2 $ by simp [linear_independent.total_equiv]

/-- Isomorphism between the two modules, given two modules `M` and `M'` with respective bases
`v` and `v'` and a bijection between the indexing sets of the two bases. -/
def linear_equiv_of_is_basis {v : ι → M} {v' : ι' → M'} (hv : is_basis R v) (hv' : is_basis R v')
  (e : ι ≃ ι') : M ≃ₗ[R] M' :=
{ inv_fun := hv'.constr (v ∘ e.symm),
  left_inv := have (hv'.constr (v ∘ e.symm)).comp (hv.constr (v' ∘ e)) = linear_map.id,
      from hv.ext $ by simp,
    λ x, congr_arg (λ h : M →ₗ[R] M, h x) this,
  right_inv := have (hv.constr (v' ∘ e)).comp (hv'.constr (v ∘ e.symm)) = linear_map.id,
      from hv'.ext $ by simp,
    λ y, congr_arg (λ h : M' →ₗ[R] M', h y) this,
  ..hv.constr (v' ∘ e) }

lemma is_basis_inl_union_inr {v : ι → M} {v' : ι' → M'}
  (hv : is_basis R v) (hv' : is_basis R v') :
  is_basis R (sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) :=
begin
  split,
  apply linear_independent_inl_union_inr' hv.1 hv'.1,
  rw [sum.elim_range, span_union,
      set.range_comp, span_image (inl R M M'), hv.2,  map_top,
      set.range_comp, span_image (inr R M M'), hv'.2, map_top],
  exact linear_map.sup_range_inl_inr
end

end is_basis

lemma is_basis_singleton_one (R : Type*) [unique ι] [ring R] :
  is_basis R (λ (_ : ι), (1 : R)) :=
begin
  split,
  { refine linear_independent_iff.2 (λ l hl, _),
    rw [finsupp.total_unique, smul_eq_mul, mul_one] at hl,
    exact finsupp.unique_ext hl },
  { refine top_unique (λ _ _, _),
    simp only [mem_span_singleton, range_const, mul_one, exists_eq, smul_eq_mul] }
end

protected lemma linear_equiv.is_basis (hs : is_basis R v)
  (f : M ≃ₗ[R] M') : is_basis R (f ∘ v) :=
begin
  split,
  { simpa only using hs.1.map' (f : M →ₗ[R] M') f.ker },
  { rw [set.range_comp, ← linear_equiv.coe_coe, span_image, hs.2, map_top, f.range] }
end

lemma is_basis_span (hs : linear_independent R v) :
  @is_basis ι R (span R (range v)) (λ i : ι, ⟨v i, subset_span (mem_range_self _)⟩) _ _ _ :=
begin
split,
{ apply linear_independent_span hs },
{ rw eq_top_iff',
  intro x,
  have h₁ : subtype.val '' set.range (λ i, subtype.mk (v i) _) = range v,
    by rw ←set.range_comp,
  have h₂ : map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _)))
              = span R (range v),
    by rw [←span_image, submodule.subtype_eq_val, h₁],
  have h₃ : (x : M) ∈ map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _))),
    by rw h₂; apply subtype.mem x,
  rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩,
  have h_x_eq_y : x = y,
    by rw [subtype.ext_iff, ← hy₂]; simp,
  rw h_x_eq_y,
  exact hy₁ }
end

lemma is_basis_empty (h_empty : ¬ nonempty ι) (h : ∀x:M, x = 0) : is_basis R (λ x : ι, (0 : M)) :=
⟨ linear_independent_empty_type h_empty,
  eq_top_iff'.2 $ assume x, (h x).symm ▸ submodule.zero_mem _ ⟩

lemma is_basis_empty_bot (h_empty : ¬ nonempty ι) :
  is_basis R (λ _ : ι, (0 : (⊥ : submodule R M))) :=
begin
  apply is_basis_empty h_empty,
  intro x,
  apply subtype.ext_iff_val.2,
  exact (submodule.mem_bot R).1 (subtype.mem x),
end

open fintype
variables [fintype ι] (h : is_basis R v)

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def is_basis.equiv_fun : M ≃ₗ[R] (ι → R) :=
linear_equiv.trans (module_equiv_finsupp h)
  { to_fun := finsupp.to_fun,
    map_add' := λ x y, by ext; exact finsupp.add_apply,
    map_smul' := λ x y, by ext; exact finsupp.smul_apply,
    ..finsupp.equiv_fun_on_fintype }

/-- A module over a finite ring that admits a finite basis is finite. -/
def module.fintype_of_fintype [fintype R] : fintype M :=
fintype.of_equiv _ h.equiv_fun.to_equiv.symm

theorem module.card_fintype [fintype R] [fintype M] :
  card M = (card R) ^ (card ι) :=
calc card M = card (ι → R)    : card_congr h.equiv_fun.to_equiv
        ... = card R ^ card ι : card_fun

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp] lemma is_basis.equiv_fun_symm_apply (x : ι → R) :
  h.equiv_fun.symm x = ∑ i, x i • v i :=
begin
  change finsupp.sum
      ((finsupp.equiv_fun_on_fintype.symm : (ι → R) ≃ (ι →₀ R)) x) (λ (i : ι) (a : R), a • v i)
    = ∑ i, x i • v i,
  dsimp [finsupp.equiv_fun_on_fintype, finsupp.sum],
  rw finset.sum_filter,
  refine finset.sum_congr rfl (λi hi, _),
  by_cases H : x i = 0; simp [H]
end

lemma is_basis.equiv_fun_apply (u : M) : h.equiv_fun u = h.repr u := rfl

lemma is_basis.equiv_fun_total (u : M) : ∑ i, h.equiv_fun u i • v i = u:=
begin
  conv_rhs { rw ← h.total_repr u },
  simp [finsupp.total_apply, finsupp.sum_fintype, h.equiv_fun_apply]
end

@[simp]
lemma is_basis.equiv_fun_self (i j : ι) : h.equiv_fun (v i) j = if i = j then 1 else 0 :=
by { rw [h.equiv_fun_apply, h.repr_self_apply] }

@[simp] theorem is_basis.constr_apply_fintype (f : ι → M') (x : M) :
  (h.constr f : M → M') x = ∑ i, (h.equiv_fun x i) • f i :=
by simp [h.constr_apply, h.equiv_fun_apply, finsupp.sum_fintype]

end module

section vector_space

variables [field K] [add_comm_group V] [add_comm_group V'] [vector_space K V] [vector_space K V']
variables {v : ι → V} {s t : set V} {x y z : V}

include K

open submodule

lemma exists_subset_is_basis (hs : linear_independent K (λ x, x : s → V)) :
  ∃b, s ⊆ b ∧ is_basis K (coe : b → V) :=
let ⟨b, hb₀, hx, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨ b, hx,
  @linear_independent.restrict_of_comp_subtype _ _ _ id _ _ _ _ hb₃,
  by simp; exact eq_top_iff.2 hb₂⟩

lemma exists_sum_is_basis (hs : linear_independent K v) :
  ∃ (ι' : Type u) (v' : ι' → V), is_basis K (sum.elim v v') :=
begin
  -- This is a hack: we jump through hoops to reuse `exists_subset_is_basis`.
  let s := set.range v,
  let e : ι ≃ s := equiv.set.range v hs.injective,
  have : (λ x, x : s → V) = v ∘ e.symm := by { funext, dsimp, rw [equiv.set.apply_range_symm v], },
  have : linear_independent K (λ x, x : s → V),
  { rw this,
    exact linear_independent.comp hs _ (e.symm.injective), },
  obtain ⟨b, ss, is⟩ := exists_subset_is_basis this,
  let e' : ι ⊕ (b \ s : set V) ≃ b :=
  calc ι ⊕ (b \ s : set V) ≃ s ⊕ (b \ s : set V) : equiv.sum_congr e (equiv.refl _)
                       ... ≃ b                   : equiv.set.sum_diff_subset ss,
  refine ⟨(b \ s : set V), λ x, x.1, _⟩,
  convert is_basis.comp is e' _,
  { funext x,
    cases x; simp; refl, },
  { exact e'.bijective, },
end

variables (K V)
lemma exists_is_basis : ∃b : set V, is_basis K (λ i, i : b → V) :=
let ⟨b, _, hb⟩ := exists_subset_is_basis (linear_independent_empty K V : _) in ⟨b, hb⟩
variables {K V}

lemma linear_map.exists_left_inverse_of_injective (f : V →ₗ[K] V')
  (hf_inj : f.ker = ⊥) : ∃g:V' →ₗ V, g.comp f = linear_map.id :=
begin
  rcases exists_is_basis K V with ⟨B, hB⟩,
  have hB₀ : _ := hB.1.to_subtype_range,
  have : linear_independent K (λ x, x : f '' B → V'),
  { have h₁ := hB₀.image_subtype
      (show disjoint (span K (range (λ i : B, i.val))) (linear_map.ker f), by simp [hf_inj]),
    rwa subtype.range_coe at h₁ },
  rcases exists_subset_is_basis this with ⟨C, BC, hC⟩,
  haveI : inhabited V := ⟨0⟩,
  use hC.constr (C.restrict (inv_fun f)),
  refine hB.ext (λ b, _),
  rw image_subset_iff at BC,
  have : f b = (⟨f b, BC b.2⟩ : C) := rfl,
  dsimp,
  rw [this, constr_basis hC],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _
end

lemma submodule.exists_is_compl (p : submodule K V) : ∃ q : submodule K V, is_compl p q :=
let ⟨f, hf⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype in
⟨f.ker, linear_map.is_compl_of_proj $ linear_map.ext_iff.1 hf⟩

instance vector_space.submodule.is_complemented : is_complemented (submodule K V) :=
⟨submodule.exists_is_compl⟩

lemma linear_map.exists_right_inverse_of_surjective (f : V →ₗ[K] V')
  (hf_surj : f.range = ⊤) : ∃g:V' →ₗ V, f.comp g = linear_map.id :=
begin
  rcases exists_is_basis K V' with ⟨C, hC⟩,
  haveI : inhabited V := ⟨0⟩,
  use hC.constr (C.restrict (inv_fun f)),
  refine hC.ext (λ c, _),
  simp [constr_basis hC, right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) c]
end

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
lemma linear_map.exists_extend {p : submodule K V} (f : p →ₗ[K] V') :
  ∃ g : V →ₗ[K] V', g.comp p.subtype = f :=
let ⟨g, hg⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype in
⟨f.comp g, by rw [linear_map.comp_assoc, hg, f.comp_id]⟩

open submodule linear_map

/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
lemma submodule.exists_le_ker_of_lt_top (p : submodule K V) (hp : p < ⊤) :
  ∃ f ≠ (0 : V →ₗ[K] K), p ≤ ker f :=
begin
  rcases submodule.exists_of_lt hp with ⟨v, -, hpv⟩, clear hp,
  rcases (linear_pmap.sup_span_singleton ⟨p, 0⟩ v (1 : K) hpv).to_fun.exists_extend with ⟨f, hf⟩,
  refine ⟨f, _, _⟩,
  { rintro rfl, rw [linear_map.zero_comp] at hf,
    have := linear_pmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv 0 p.zero_mem 1,
    simpa using (linear_map.congr_fun hf _).trans this },
  { refine λ x hx, mem_ker.2 _,
    have := linear_pmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv x hx 0,
    simpa using (linear_map.congr_fun hf _).trans this }
end

theorem quotient_prod_linear_equiv (p : submodule K V) :
  nonempty ((p.quotient × p) ≃ₗ[K] V) :=
let ⟨q, hq⟩ := p.exists_is_compl in nonempty.intro $
((quotient_equiv_of_is_compl p q hq).prod (linear_equiv.refl _ _)).trans
  (prod_equiv_of_is_compl q p hq.symm)

open fintype
variables (K) (V)

theorem vector_space.card_fintype [fintype K] [fintype V] :
  ∃ n : ℕ, card V = (card K) ^ n :=
exists.elim (exists_is_basis K V) $ λ b hb, ⟨card b, module.card_fintype hb⟩

end vector_space
