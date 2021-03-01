/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import analysis.calculus.specific_functions
import geometry.manifold.times_cont_mdiff

variables
{E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{F : Type*} [inner_product_space ℝ F]
{H : Type*} [topological_space H]
(IE : model_with_corners ℝ E H) (IF : model_with_corners ℝ F H)
{M : Type*} [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners IE M]

open function set metric filter
open_locale topological_space manifold classical filter

noncomputable theory

def msmooth_bump_function (x : M) (r R : ℝ) : M → ℝ :=
indicator (ext_chart_at IF x).source
  (smooth_bump_function (ext_chart_at IF x x) r R ∘ ext_chart_at IF x)

namespace msmooth_bump_function

variables {x y : M} {r R : ℝ}

lemma eq_on_source :
  eq_on (msmooth_bump_function IF x r R)
    (smooth_bump_function (ext_chart_at IF x x) r R ∘ ext_chart_at IF x)
    (ext_chart_at IF x).source :=
eq_on_indicator

lemma eventually_eq_of_mem_source (hy : y ∈ (ext_chart_at IF x).source) :
  msmooth_bump_function IF x r R =ᶠ[𝓝 y]
    smooth_bump_function (ext_chart_at IF x x) r R ∘ ext_chart_at IF x :=
mem_nhds_sets_iff.2 ⟨_, eq_on_source IF, ext_chart_at_open_source _ _, hy⟩

lemma one_of_dist_le (hlt : r < R) (hs : y ∈ (ext_chart_at IF x).source)
  (hd : dist (ext_chart_at IF x y) (ext_chart_at IF x x) ≤ r) :
  msmooth_bump_function IF x r R y = 1 :=
by simp only [eq_on_source IF hs, (∘),
  smooth_bump_function.one_of_mem_closed_ball hd hlt]

lemma support_eq_inter_preimage (hrR : r < R) :
  support (msmooth_bump_function IF x r R) =
    (ext_chart_at IF x).source ∩ (ext_chart_at IF x ⁻¹' ball (ext_chart_at IF x x) R) :=
by rw [msmooth_bump_function, support_indicator, (∘), support_comp_eq_preimage,
  ← (ext_chart_at IF x).symm_image_inter_target_eq',
  ← (ext_chart_at IF x).symm_image_inter_target_eq', smooth_bump_function.support_eq hrR]

lemma support_eq_symm_image (hrR : r < R)
  (hR : ball (ext_chart_at IF x x) R ∩ range IF ⊆ (ext_chart_at IF x).target) :
  support (msmooth_bump_function IF x r R) =
    (ext_chart_at IF x).symm '' (ball (ext_chart_at IF x x) R ∩ range IF) :=
begin
  rw [support_eq_inter_preimage IF hrR, ← (ext_chart_at IF x).symm_image_inter_target_eq'],
  congr' 1,
  ext y,
  exact ⟨λ hy, ⟨hy.1, ext_chart_at_target_subset_range IF x hy.2⟩, λ hy, ⟨hy.1, hR hy⟩⟩
end

lemma mem_Icc : msmooth_bump_function IF x r R y ∈ Icc (0 : ℝ) 1 :=
begin
  have : msmooth_bump_function IF x r R y = 0 ∨ msmooth_bump_function IF x r R y = _,
    from indicator_eq_zero_or_self _ _ _,
  cases this; rw this,
  exacts [left_mem_Icc.2 zero_le_one, ⟨smooth_bump_function.nonneg, smooth_bump_function.le_one⟩]
end

lemma nonneg : 0 ≤ msmooth_bump_function IF x r R y := (mem_Icc IF).1

lemma le_one : msmooth_bump_function IF x r R y ≤ 1 := (mem_Icc IF).2

lemma eventually_eq_one_of_dist_lt (hlt : r < R) (hs : y ∈ (ext_chart_at IF x).source)
  (hd : dist (ext_chart_at IF x y) (ext_chart_at IF x x) < r) :
  msmooth_bump_function IF x r R =ᶠ[𝓝 y] (λ _, 1) :=
begin
  filter_upwards [mem_nhds_sets (ext_chart_preimage_open_of_open IF x is_open_ball) ⟨hs, hd⟩],
  rintro z ⟨hzs, hzd : _ < _⟩,
  exact one_of_dist_le IF hlt hzs hzd.le
end

lemma eventually_eq_one (h0 : 0 < r) (hlt : r < R) :
  msmooth_bump_function IF x r R =ᶠ[𝓝 x] (λ _, 1) :=
eventually_eq_one_of_dist_lt IF hlt (mem_ext_chart_source _ _) $ by rwa dist_self

variables [t2_space M] [finite_dimensional ℝ F]

lemma closure_support_subset_symm_image_closed_ball (hrR : r < R)
  (hR : closed_ball (ext_chart_at IF x x) R ∩ range IF ⊆ (ext_chart_at IF x).target) :
  closure (support (msmooth_bump_function IF x r R)) ⊆
    (ext_chart_at IF x).symm '' (closed_ball (ext_chart_at IF x x) R ∩ range IF) :=
begin
  have hR' : ball (ext_chart_at IF x x) R ∩ range IF ⊆ (ext_chart_at IF x).target,
    from subset.trans (inter_subset_inter_left _ ball_subset_closed_ball) hR,
  rw [support_eq_symm_image IF hrR hR'],
  exact closure_minimal (image_subset _ $ inter_subset_inter_left _ ball_subset_closed_ball)
    (compact_ext_chart_symm_image_closed_ball IF x hR).is_closed
end

lemma closure_support_subset_source (hrR : r < R)
  (hR : closed_ball (ext_chart_at IF x x) R ∩ range IF ⊆ (ext_chart_at IF x).target) :
  closure (support (msmooth_bump_function IF x r R)) ⊆ (ext_chart_at IF x).source :=
calc closure (support (msmooth_bump_function IF x r R))
    ⊆ (ext_chart_at IF x).symm '' (closed_ball (ext_chart_at IF x x) R ∩ range IF) :
  closure_support_subset_symm_image_closed_ball IF hrR hR
... ⊆ (ext_chart_at IF x).symm '' (ext_chart_at IF x).target :
  image_subset _ hR
... = (ext_chart_at IF x).source : (ext_chart_at IF x).symm_image_target_eq_source

lemma compact_closure_support (hrR : r < R)
  (hR : closed_ball (ext_chart_at IF x x) R ∩ range IF ⊆ (ext_chart_at IF x).target) :
  is_compact (closure $ support $ msmooth_bump_function IF x r R) :=
compact_of_is_closed_subset (compact_ext_chart_symm_image_closed_ball IF x hR) is_closed_closure $
 closure_support_subset_symm_image_closed_ball IF hrR hR

protected lemma smooth [smooth_manifold_with_corners IF M] (h0 : 0 < r) (hrR : r < R)
  (hR : closed_ball (ext_chart_at IF x x) R ∩ range IF ⊆ (ext_chart_at IF x).target) :
  smooth IF 𝓘(ℝ) (msmooth_bump_function IF x r R) :=
begin
  intro y,
  by_cases hy : y ∈ closure (support $ msmooth_bump_function IF x r R),
  { have hy : y ∈ (ext_chart_at IF x).source, from closure_support_subset_source IF hrR hR hy,
    refine times_cont_mdiff_at.congr_of_eventually_eq _ (eventually_eq_of_mem_source _ hy),
    exact (smooth_bump_function.times_cont_diff_at h0 hrR).times_cont_mdiff_at.comp y
      (times_cont_mdiff_at_ext_chart_at' hy) },
  { refine times_cont_mdiff_at.congr_of_eventually_eq _ (eventually_eq_zero_nhds.2 hy),
    exact times_cont_mdiff_at_const }
end

end msmooth_bump_function
