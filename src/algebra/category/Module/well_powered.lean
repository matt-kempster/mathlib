/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Module.basic
import category_theory.subobject.well_powered

/-!
# The category of `R`-modules is well-powered
-/

open category_theory

universes v u

namespace Module
variables {R : Type u} [ring R] (M : Module.{v} R)

noncomputable def subobject_Module : subobject M ≃ submodule R M :=
{ to_fun := λ S, S.arrow.range,
  inv_fun := λ N, subobject.mk $ as_hom' $ N.subtype,
  left_inv := λ S,
  begin
    dsimp,
    symmetry,
    apply subobject.eq_of_comm₁,
    swap,
    apply linear_equiv.to_Module_iso'',
    apply linear_equiv.of_bijective (linear_map.cod_restrict S.arrow.range S.arrow (linear_map.mem_range_self (subobject.arrow S))),
    { rw linear_map.ker_cod_restrict,
      exact ker_eq_bot_of_mono _ },
    { rw linear_map.range_cod_restrict,
      simp only [submodule.comap_subtype_self] },
    ext,
    refl
  end,
  right_inv := λ N,
  begin
    dsimp,
    have := congr_arg linear_map.range (subobject.underlying_iso_arrow (as_hom' N.subtype)),
    let q := category_theory.iso.to_linear_equiv (subobject.underlying_iso (as_hom' N.subtype)).symm,
    have ht : (q.to_linear_map : _ →ₗ _) = (subobject.underlying_iso (as_hom' N.subtype)).inv,
    { ext, refl },
    rw [←ht, coe_comp'] at this,
    erw linear_equiv.range_comp at this,
    rw this,
    exact submodule.range_subtype _,
  end }

lemma well_powered_Module : well_powered (Module.{v} R) :=
⟨λ M, ⟨⟨submodule R M, subobject_Module _, trivial⟩⟩⟩

end Module
