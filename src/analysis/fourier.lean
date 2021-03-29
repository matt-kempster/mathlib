/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import measure_theory.l2_space
import measure_theory.haar_measure
import geometry.manifold.instances.circle

/-!

# Fourier analysis on the circle

-/

noncomputable theory
open topological_space continuous_map measure_theory measure_theory.measure

local attribute [instance] fact_one_le_two_ennreal

section haar_circle
/-! We make the circle into a measure space, using the Haar measure normalized to have total
measure 1. -/

instance : measurable_space circle := borel circle
instance : borel_space circle := ⟨rfl⟩

/-- Haar measure on the circle, normalized to have total measure 1. -/
def haar_circle : measure circle := haar_measure positive_compacts_univ

instance : probability_measure haar_circle := ⟨haar_measure_self⟩

instance : measure_space circle :=
{ volume := haar_circle,
  .. circle.measurable_space }

end haar_circle

section fourier

/-- The family of monomials `λ z, z ^ n`, parametrized by `n : ℤ` and considered as bundled
continuous maps from `circle` to `ℂ`. -/
def fourier (n : ℤ) : C(circle, ℂ) :=
{ to_fun := λ z, z ^ n,
  continuous_to_fun := begin
    rw continuous_iff_continuous_at,
    intros z,
    exact (continuous_at_fpow (nonzero_of_mem_circle z) n).comp
      continuous_subtype_coe.continuous_at,
  end }

@[simp] lemma fourier_apply {n : ℤ} {z : circle} : fourier n z = z ^ n := rfl

@[simp] lemma fourier_zero {z : circle} : fourier 0 z = 1 := rfl

lemma conj_fourier {n : ℤ} {z : circle} : complex.conj (fourier n z) = fourier (-n) z :=
by simp [← coe_inv_circle_eq_conj z]

lemma mul_fourier {m n : ℤ} {z : circle} : (fourier m z) * (fourier n z) = fourier (m + n) z :=
by simp [fpow_add (nonzero_of_mem_circle z)]

lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (z : circle) :
  fourier n ((exp_map_circle (n⁻¹ * real.pi) * z)) = - fourier n z :=
begin
  simp,
  rw mul_fpow,
  rw ← complex.exp_int_mul,
  transitivity (-1) * (z:ℂ) ^ n,
  { congr,
    rw ← complex.exp_pi_mul_I,
    congr' 1,
    have : (n:ℂ) ≠ 0 := by exact_mod_cast hn,
    field_simp,
    ring },
  simp,
end

lemma orthonormal_fourier : orthonormal ℂ (λ n, to_Lp ℂ 2 haar_circle ℂ (fourier n)) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp haar_circle (fourier i) (fourier j),
  split_ifs,
  { simp [h, probability_measure.measure_univ, conj_fourier, mul_fourier, -fourier_apply] },
  simp [conj_fourier, mul_fourier, -fourier_apply],
  have : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  exact integral_zero_of_mul_left_eq_neg (is_mul_left_invariant_haar_measure _)
    (fourier (-i + j)).continuous.measurable (fourier_add_half_inv_index this),
end

end fourier
