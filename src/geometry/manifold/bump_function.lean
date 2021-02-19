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
{M : Type*} [topological_space M] [t2_space M] [charted_space H M]
  [smooth_manifold_with_corners I M]

open function set metric filter
open_locale topological_space manifold classical filter

lemma exists_smooth_bump_function {x : M} {s : set M} (hs : s ∈ 𝓝 x) :
  ∃ f : M → ℝ, f =ᶠ[𝓝 x] 1 ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ smooth I 𝓘(ℝ) f ∧
    is_compact (closure $ support f) ∧ closure (support f) ⊆ s ∩ (ext_chart_at I x).source :=
begin
  /- This proof uses `e := ext_chart_at I x` to transfer the statement of
  `exists_times_cont_diff_bump_function_of_mem_nhds` from `E` to `M`. -/
  set e : local_equiv M E := ext_chart_at I x,
  /- To avoid dealing with `closure`s, we replace `s` with a smaller compact neighborhood `K`.
  We also ensure `K ⊆ (ext_chart_at I x).source`. -/
  haveI := I.locally_compact,
  haveI : locally_compact_space M := charted_space.locally_compact H,
  obtain ⟨K, hKx, hKxs, hKc⟩ : ∃ K ∈ 𝓝 x, K ⊆ s ∩ e.source ∧ is_compact K,
    from locally_compact_space.local_compact_nhds _ _
      (inter_mem_sets hs (ext_chart_at_source_mem_nhds I _)),
  suffices : ∃ f : M → ℝ,
    f =ᶠ[𝓝 x] 1 ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ smooth I 𝓘(ℝ) f ∧ support f ⊆ K,
  { rcases this with ⟨f, hf1, hf01, hfs, hfK⟩,
    replace hfK : closure (support f) ⊆ K, from closure_minimal hfK hKc.is_closed,
    exact ⟨f, hf1, hf01, hfs, compact_of_is_closed_subset hKc is_closed_closure hfK,
      subset.trans hfK hKxs⟩ },
  have hKe : K ⊆ e.source := (subset_inter_iff.1 hKxs).2,
  clear_dependent s,
  /- Now we apply the lemma about normed finite dimensional spaces to the set
    `e '' K ∪ (range I)ᶜ` (more precisely, to `{y | y ∈ range I → y ∈ e '' K}`). -/
  have : e '' K ∈ 𝓝[range I] (e x), from ext_chart_at_map_nhds I x ▸ image_mem_map hKx,
  rcases exists_times_cont_diff_bump_function_of_mem_nhds (mem_inf_principal.1 this)
    with ⟨g, h1, h01, htcd, hsc, hsupp⟩,
  /- The restriction of `g ∘ e` to `e.source` satisfies all the requirements. We need to use
  `set.indicator` here because `e` can send some points outside of `e.source` to the support
  of `g`. -/
  set f : M → ℝ := e.source.indicator (g ∘ e),
  have A : ∀ x' ∈ e.source, f =ᶠ[𝓝 x'] g ∘ e,
    from λ x' hx', eq_on_indicator.eventually_eq_of_mem (ext_chart_at_source_mem_nhds' _ _ hx'),
  have B : support f ⊆ K,
  { rw [support_indicator],
    rintro x' ⟨hx'e, hx'g : g (e x') ≠ 0⟩,
    have : e x' ∈ e '' K, from hsupp (subset_closure hx'g) (mem_range_self _),
    exact e.inj_on.mem_of_mem_image hKe hx'e this },
  refine ⟨f, _, _, _, B⟩,
  { exact (A x $ mem_ext_chart_source _ _).trans ((ext_chart_at_continuous_at I x).eventually h1) },
  { intro y,
    obtain (h|h) : f y = 0 ∨ f y = _ := indicator_eq_zero_or_self _ _ _,
    { simp only [h, left_mem_Icc, zero_le_one] },
    { simp only [h, h01] } },
  { intro x',
    by_cases h : x' ∈ e.source,
    { -- If `x' ∈ e.source`, then `f = g ∘ e` in a neighborhood of `x'`, and both functions in the
      -- composition are smooth
      refine times_cont_mdiff_at.congr_of_eventually_eq _ (A x' h),
      refine htcd.times_cont_diff_at.times_cont_mdiff_at.comp x'
        (times_cont_mdiff_at_ext_chart_at' _),
      rwa ext_chart_at_source at h },
    { -- otherwise, `f = 0` in a neighborhood of `x'`.
      have : f =ᶠ[𝓝 x'] (λ _, 0),
      { have : x' ∉ K, from compl_subset_compl.2 hKe h,
        filter_upwards [mem_nhds_sets hKc.is_closed this],
        exact λ z hz, nmem_support.1 (compl_subset_compl.2 B hz) },
      exact times_cont_mdiff_at_const.congr_of_eventually_eq this } },
end
