/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import analysis.calculus.specific_functions
import geometry.manifold.times_cont_mdiff

variables
{E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{H : Type*} [topological_space H]
(I : model_with_corners ℝ E H)
{M : Type*} [topological_space M] [t2_space M] [charted_space H M] [smooth_manifold_with_corners I M]
-- TODO: can we deduce `t2_space` from other assumptions?

open function set metric filter
open_locale topological_space manifold classical filter

lemma exists_smooth_bump_function {x : M} {s : set M} (hs : s ∈ 𝓝 x) :
  ∃ f : M → ℝ, f =ᶠ[𝓝 x] 1 ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ smooth I 𝓘(ℝ) f ∧
    is_compact (closure $ support f) ∧ closure (support f) ⊆ s ∩ (ext_chart_at I x).source :=
begin
  set e : local_equiv M E := ext_chart_at I x,
  have : e '' (s ∩ e.source) ∈ 𝓝[range I] (e x),
  { rw ← ext_chart_at_map_nhds,
    exact image_mem_map (inter_mem_sets hs (ext_chart_at_source_mem_nhds _ _)) },
  rcases exists_times_cont_diff_bump_function_of_mem_nhds (mem_inf_principal.1 this)
    with ⟨g, h1, h01, htcd, hsc, hsupp⟩,
  set f : M → ℝ := e.source.indicator (g ∘ e),
  have hsupp_eq : support f = e.symm '' (support g ∩ e.target),
  { rw [e.symm_image_inter_target_eq, support_indicator, support_comp_eq_preimage,
      preimage_inter, ← inter_assoc],
    refine (inter_eq_self_of_subset_left $ λ x hx, _).symm,
    exact e.map_source hx.1 },
  have A : closure (support g) ∩ range I ⊆ e.target,
  { rintro y ⟨hgy, hy⟩,
    rw [← e.image_source_eq_target],
    exact image_subset _ (inter_subset_right _ _) (hsupp hgy hy) },
  have B : is_compact (e.symm '' (closure (support g) ∩ range I)),
  { refine (hsc.inter_right I.is_closed_range).image_of_continuous_on _,
    refine (ext_chart_continuous_on_symm _ _).mono A },
  have C : closure (support f) ⊆ e.symm '' (closure (support g) ∩ range I),
  { refine closure_minimal _ B.is_closed,
    rw hsupp_eq,
    exact image_subset _
      (inter_subset_inter subset_closure (ext_chart_at_target_subset_range _ _)) },
  have D : closure (support f) ⊆ s ∩ e.source,
  { refine subset.trans C _,
    rw e.symm_image_eq_source_inter_preimage A,
    rintro x' ⟨hsrc, hx'g, hx'I⟩,
    have : e x' ∈ e '' (s ∩ e.source), from hsupp hx'g hx'I,
    rw [e.image_inter_source_eq, mem_inter_iff, mem_preimage, e.left_inv hsrc] at this,
    exact this.2 },
  have E : ∀ x' ∈ e.source, f =ᶠ[𝓝 x'] g ∘ e,
    from λ x' hx', eq_on_indicator.eventually_eq_of_mem (ext_chart_at_source_mem_nhds' _ _ hx'),
  refine ⟨f, _, _, _, _, _⟩,
  { exact (E x $ mem_ext_chart_source _ _).trans ((ext_chart_at_continuous_at I x).eventually h1) },
  { intro y,
    obtain (h|h) : f y = 0 ∨ f y = _ := indicator_eq_zero_or_self _ _ _,
    { simp only [h, left_mem_Icc, zero_le_one] },
    { simp only [h, h01] } },
  { intro x',
    by_cases h : x' ∈ e.source,
    { refine times_cont_mdiff_at.congr_of_eventually_eq _ (E x' h),
      refine htcd.times_cont_diff_at.times_cont_mdiff_at.comp x'
        (times_cont_mdiff_at_ext_chart_at' _),
      rwa ext_chart_at_source at h },
    { have : x' ∈ (closure (support f))ᶜ := λ h',  h (D h').2,
      rw [← interior_compl, mem_interior_iff_mem_nhds] at this,
      have : f =ᶠ[𝓝 x'] (λ _, 0) := mem_sets_of_superset this (λ y, nmem_support.1),
      refine times_cont_mdiff_at_const.congr_of_eventually_eq this } },
  { exact compact_of_is_closed_subset B is_closed_closure C },
  { exact D }
end
