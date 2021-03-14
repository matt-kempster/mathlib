/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import analysis.calculus.specific_functions
import geometry.manifold.diffeomorph

universes uE uF uH uM
variables
{E : Type uE} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{F : Type uF} [inner_product_space ℝ F]
{H : Type uH} [topological_space H]
(IE : model_with_corners ℝ E H) (IF : model_with_corners ℝ F H)
{M : Type uM} [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners IE M]

open function set metric filter finite_dimensional
open_locale topological_space manifold classical filter

noncomputable theory

variable (M)

/-- Given a smooth manifold modelled on an inner product space `F`, `f : smooth_bump_function IF M`
is a smooth function on `M` such that in the extended chart `e` at `f.c`

* `f x = 1` in the closed ball of radius `f.r` centered at `f.c`;
* `f x = 0` outside of the ball of radius `f.R` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The structure contains data required to construct a function with these properties. The function
is available as `⇑f` or `f x`. Formal statements of the properties listed above involve some
(pre)images under `ext_chart_at IF f.c` and are given as lemmas in the `msmooth_bump_function`
namespace; some of them require `F` to be finite dimensional, and some require `M` to be a Hausdorff
space. If `M` is modelled on a finite dimensional normed space without an inner product, the user
should use `msmooth_bump_function (IE.trans_equiv e) M`, where
`e : E ≃L[ℝ] euclidean_space ℝ (fin $ findim ℝ E) :=
  (continuous_linear_equiv.of_findim_eq findim_euclidean_space_fin.symm)`. -/
structure msmooth_bump_function :=
(c : M)
(r R : ℝ)
(r_pos : 0 < r)
(r_lt_R : r < R)
(closed_ball_subset : closed_ball (ext_chart_at IF c c) R ∩ range IF ⊆ (ext_chart_at IF c).target)

variable {M}

namespace msmooth_bump_function

variables (f : msmooth_bump_function IF M) {x : M} {IF}

instance : has_coe_to_fun (msmooth_bump_function IF M) :=
⟨_, λ f, indicator (ext_chart_at IF f.c).source
  (smooth_bump_function (ext_chart_at IF f.c f.c) f.r f.R ∘ ext_chart_at IF f.c)⟩

lemma coe_def : ⇑f = indicator (ext_chart_at IF f.c).source
  (smooth_bump_function (ext_chart_at IF f.c f.c) f.r f.R ∘ ext_chart_at IF f.c) :=
rfl

lemma R_pos : 0 < f.R := f.r_pos.trans f.r_lt_R

lemma ball_subset : ball (ext_chart_at IF f.c f.c) f.R ∩ range IF ⊆ (ext_chart_at IF f.c).target :=
subset.trans (inter_subset_inter_left _ ball_subset_closed_ball) f.closed_ball_subset

lemma eq_on_source :
  eq_on f
    (smooth_bump_function (ext_chart_at IF f.c f.c) f.r f.R ∘ ext_chart_at IF f.c)
    (ext_chart_at IF f.c).source :=
eq_on_indicator

lemma eventually_eq_of_mem_source (hx : x ∈ (ext_chart_at IF f.c).source) :
  f =ᶠ[𝓝 x] smooth_bump_function (ext_chart_at IF f.c f.c) f.r f.R ∘ ext_chart_at IF f.c :=
mem_nhds_sets_iff.2 ⟨_, f.eq_on_source, ext_chart_at_open_source _ _, hx⟩

lemma one_of_dist_le (hs : x ∈ (ext_chart_at IF f.c).source)
  (hd : dist (ext_chart_at IF f.c x) (ext_chart_at IF f.c f.c) ≤ f.r) :
  f x = 1 :=
by simp only [f.eq_on_source hs, (∘), smooth_bump_function.one_of_mem_closed_ball hd f.r_lt_R]

lemma support_eq_inter_preimage :
  support f =
    (ext_chart_at IF f.c).source ∩ (ext_chart_at IF f.c ⁻¹' ball (ext_chart_at IF f.c f.c) f.R) :=
by rw [coe_def, support_indicator, (∘), support_comp_eq_preimage,
  ← (ext_chart_at IF f.c).symm_image_target_inter_eq',
  ← (ext_chart_at IF f.c).symm_image_target_inter_eq', smooth_bump_function.support_eq f.r_lt_R]

lemma support_eq_symm_image :
  support f =
    (ext_chart_at IF f.c).symm '' (ball (ext_chart_at IF f.c f.c) f.R ∩ range IF) :=
begin
  rw [f.support_eq_inter_preimage, ← (ext_chart_at IF f.c).symm_image_target_inter_eq',
    inter_comm],
  congr' 1,
  ext y,
  exact and.congr_right_iff.2
    (λ hy, ⟨λ h, ext_chart_at_target_subset_range _ _ h, λ h, f.ball_subset ⟨hy, h⟩⟩)
end

lemma support_subset_source : support f ⊆ (chart_at H f.c).source :=
by { rw [f.support_eq_inter_preimage, ← ext_chart_at_source IF], exact inter_subset_left _ _ }

lemma mem_Icc : f x ∈ Icc (0 : ℝ) 1 :=
begin
  have : f x = 0 ∨ f x = _, from indicator_eq_zero_or_self _ _ _,
  cases this; rw this,
  exacts [left_mem_Icc.2 zero_le_one, ⟨smooth_bump_function.nonneg, smooth_bump_function.le_one⟩]
end

lemma nonneg : 0 ≤ f x := f.mem_Icc.1

lemma le_one : f x ≤ 1 := f.mem_Icc.2

lemma eventually_eq_one_of_dist_lt (hs : x ∈ (ext_chart_at IF f.c).source)
  (hd : dist (ext_chart_at IF f.c x) (ext_chart_at IF f.c f.c) < f.r) :
  f =ᶠ[𝓝 x] (λ _, 1) :=
begin
  filter_upwards [mem_nhds_sets (ext_chart_preimage_open_of_open IF f.c is_open_ball) ⟨hs, hd⟩],
  rintro z ⟨hzs, hzd : _ < _⟩,
  exact f.one_of_dist_le hzs hzd.le
end

lemma eventually_eq_one : f =ᶠ[𝓝 f.c] (λ _, 1) :=
f.eventually_eq_one_of_dist_lt (mem_ext_chart_source _ _) $ by { rw dist_self, exact f.r_pos }

@[simp] lemma eq_one : f f.c = 1 := f.eventually_eq_one.eq_of_nhds

lemma c_mem_support : f.c ∈ support f := by { rw [mem_support, f.eq_one], exact one_ne_zero }

lemma nonempty_support : (support f).nonempty := ⟨f.c, f.c_mem_support⟩

section findim_F

variables [finite_dimensional ℝ F]

lemma compact_symm_image_closed_ball :
  is_compact ((ext_chart_at IF f.c).symm ''
    (closed_ball (ext_chart_at IF f.c f.c) f.R ∩ range IF)) :=
compact_ext_chart_symm_image_closed_ball IF f.c f.closed_ball_subset

variables [t2_space M]

lemma closure_support_subset_symm_image_closed_ball :
  closure (support f) ⊆
    (ext_chart_at IF f.c).symm '' (closed_ball (ext_chart_at IF f.c f.c) f.R ∩ range IF) :=
begin
  rw support_eq_symm_image,
  exact closure_minimal (image_subset _ $ inter_subset_inter_left _ ball_subset_closed_ball)
    f.compact_symm_image_closed_ball.is_closed
end

lemma closure_support_subset_ext_chart_at_source :
  closure (support f) ⊆ (ext_chart_at IF f.c).source :=
calc closure (support f)
    ⊆ (ext_chart_at IF f.c).symm '' (closed_ball (ext_chart_at IF f.c f.c) f.R ∩ range IF) :
  f.closure_support_subset_symm_image_closed_ball
... ⊆ (ext_chart_at IF f.c).symm '' (ext_chart_at IF f.c).target :
  image_subset _ f.closed_ball_subset
... = (ext_chart_at IF f.c).source : (ext_chart_at IF f.c).symm_image_target_eq_source

lemma closure_support_subset_chart_at_source :
  closure (support f) ⊆ (chart_at H f.c).source :=
by simpa only [ext_chart_at_source] using f.closure_support_subset_ext_chart_at_source

lemma compact_closure_support : is_compact (closure $ support f) :=
compact_of_is_closed_subset f.compact_symm_image_closed_ball is_closed_closure
 f.closure_support_subset_symm_image_closed_ball

protected lemma smooth' [smooth_manifold_with_corners IF M] : smooth IF 𝓘(ℝ) f :=
begin
  refine times_cont_mdiff_of_support (λ x hx, _),
  have := f.closure_support_subset_ext_chart_at_source hx,
  refine times_cont_mdiff_at.congr_of_eventually_eq _
    (f.eq_on_source.eventually_eq_of_mem $ ext_chart_at_source_mem_nhds' _ _ this),
  exact (smooth_bump_function.times_cont_diff_at f.r_pos f.r_lt_R).times_cont_mdiff_at.comp _
    (times_cont_mdiff_at_ext_chart_at' this)
end

end findim_F

variable {IE}

protected lemma smooth [t2_space M] {e : E ≃L[ℝ] F}
  (f : msmooth_bump_function (IE.trans_diffeomorph e.to_diffeomorph) M) : smooth IE 𝓘(ℝ) f :=
begin
  haveI : finite_dimensional ℝ F := e.to_linear_equiv.finite_dimensional,
  exact e.to_diffeomorph.smooth_trans_diffeomorph_left.1 f.smooth'
end

protected lemma smooth_at [t2_space M] {e : E ≃L[ℝ] F}
  (f : msmooth_bump_function (IE.trans_diffeomorph e.to_diffeomorph) M) {x} :
  smooth_at IE 𝓘(ℝ) f x :=
f.smooth.smooth_at

lemma smooth_smul {G} [normed_group G] [normed_space ℝ G] [t2_space M] {e : E ≃L[ℝ] F}
  (f : msmooth_bump_function (IE.trans_diffeomorph e.to_diffeomorph) M)
  {g : M → G} (hg : smooth_on IE 𝓘(ℝ, G) g (ext_chart_at IE f.c).source) :
  smooth IE 𝓘(ℝ, G) (λ x, f x • g x) :=
begin
  haveI : finite_dimensional ℝ F := e.to_linear_equiv.finite_dimensional,
  apply times_cont_mdiff_of_support (λ x hx, _),
  have : x ∈ (ext_chart_at IE f.c).source,
  calc x ∈ closure (support (λ x, f x • g x)) : hx
  ... ⊆ closure (support f) :
    closure_mono (support_smul_subset_left _ _)
  ... ⊆ (chart_at _ f.c).source :
    f.closure_support_subset_chart_at_source
  ... ⊆ (ext_chart_at IE f.c).source : by rw ext_chart_at_source,
  exact f.smooth_at.smul ((hg _ this).times_cont_mdiff_at $
    mem_nhds_sets (ext_chart_at_open_source _ _) this)
end

end msmooth_bump_function

/-- We say that a collection of `smooth_bump_function`s is a `smooth_bump_covering` of a set `s`
subordinate to `U : M → set M`, if

* `(f i).c ∈ s` for all `i`;
* the family `λ i, support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;
* `closure (support (f i)) ⊆ U (f i).c` for all `i`.

If `M` is a sigma-compact Hausdorff space, then a choice of `smooth_bump_covering` is available
as `smooth_bump_covering.choice_set`, see also `smooth_bump_covering.choice` for the case
`s = univ`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
structure smooth_bump_covering (s : set M) (U : M → set M) :=
(ι : Type uM)
(e : E ≃L[ℝ] euclidean_space ℝ (fin $ findim ℝ E) :=
  (continuous_linear_equiv.of_findim_eq findim_euclidean_space_fin.symm))
(to_fun : ι → msmooth_bump_function (IE.trans_equiv e) M)
(c_mem' : ∀ i, (to_fun i).c ∈ s)
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(eventually_eq_one' : ∀ x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1)
(closure_support_subset' : ∀ i, closure (support $ to_fun i) ⊆ U (to_fun i).c)

namespace smooth_bump_covering

/-- Choice of a covering of a closed set `s` by supports of smooth bump functions. -/
def choice_set [t2_space M] [sigma_compact_space M] (s : set M) (hs : is_closed s)
  (U : M → set M) (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
  smooth_bump_covering IE s U :=
begin
  apply classical.choice,
  -- First we deduce some missing instances
  haveI : locally_compact_space H := IE.locally_compact,
  haveI : locally_compact_space M := charted_space.locally_compact H,
  haveI : normal_space M := normal_of_paracompact_t2,
  /- Let `F` be the Euclidean space of the same dimension as `E`. Then `E` is diffeomorphic to `F`,
  and most of the proof will be done using `F` as a model space for `M`. -/
  set F := euclidean_space ℝ (fin $ findim ℝ E),
  have eEF : E ≃L[ℝ] F := continuous_linear_equiv.of_findim_eq findim_euclidean_space_fin.symm,
  set IF := IE.trans_diffeomorph eEF.to_diffeomorph,
  set e : M → local_equiv M F := ext_chart_at IF,
  set cBF : M → ℝ → set F := λ x r, closed_ball (e x x) r ∩ range IF,
  set cB : M → ℝ → set M := λ x r, (e x).symm '' cBF x r,
  set BF : M → ℝ → set F := λ x r, ball (e x x) r ∩ range IF,
  set B : M → ℝ → set M := λ x r, (e x).symm '' BF x r,
  have BFcBF : ∀ x r, BF x r ⊆ cBF x r,
    from λ x r, inter_subset_inter_left _ ball_subset_closed_ball,
  have BcB : ∀ x r, B x r ⊆ cB x r, from λ x r, image_subset _ (BFcBF x r),
  have hB : ∀ x ∈ s, (𝓝 x).has_basis (λ r : ℝ, 0 < r ∧ cBF x r ⊆ (e x).target ∧ cB x r ⊆ U x) (B x),
    from λ x hx, nhds_basis_ext_chart_symm_image_ball_subset _ _ (hU x hx),
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis_set hs hB
    with ⟨ι, c, R, hR, hsub', hfin⟩, choose hcs hR0 hcBFR hcBR using hR,
  have Bi_eq : ∀ i, B (c i) (R i) = (e (c i)).source ∩ e (c i) ⁻¹' ball (e (c i) (c i)) (R i),
  { intro i,
    have : ball (e (c i) (c i)) (R i) ∩ range IF ⊆ (e (c i)).target,
      from subset.trans (inter_subset_inter_left _ ball_subset_closed_ball) (hcBFR i),
    simp only [B],
    rw [← (e (c i)).symm_image_target_inter_eq', inter_comm],
    congr' 1,
    refine subset.antisymm (subset_inter (inter_subset_left _ _) this)
      (inter_subset_inter_right _ (ext_chart_at_target_subset_range _ _)) },
  have Bo : ∀ i, is_open (B (c i) (R i)),
  { intro i,
    rw Bi_eq,
    exact (ext_chart_at_continuous_on IF (c i)).preimage_open_of_open
     (ext_chart_at_open_source IF _) is_open_ball },
  have Bsrc : ∀ i, B (c i) (R i) ⊆ (e (c i)).source,
    from λ i, (Bi_eq i).symm ▸ inter_subset_left _ _,
  choose V hsV hVo hVB
    using exists_subset_Union_closure_subset hs Bo (λ x hx, hfin.point_finite x) hsub',
  have hVcB : ∀ i, closure (V i) ⊆ cB (c i) (R i), from λ i, subset.trans (hVB i) (BcB _ _),
  have hVc : ∀ i, is_compact (closure (V i)),
    from λ i, compact_of_is_closed_subset
      (compact_ext_chart_symm_image_closed_ball IF (c i) (hcBFR i)) is_closed_closure (hVcB i),
  have hVBF : ∀ i, closure (e (c i) '' V i) ⊆ BF (c i) (R i),
  { intro i,
    rw [← image_closure_of_compact (hVc i) ((ext_chart_at_continuous_on IF (c i)).mono $
      subset.trans (hVB i) (Bsrc i)), image_subset_iff],
    refine subset.trans (hVB i) (λ x' hx', mem_preimage.2 _),
    rw Bi_eq at hx',
    exact ⟨hx'.2, mem_range_self _⟩ },
  have : ∀ i, ∃ r ∈ Ioo 0 (R i), closure (e (c i) '' V i) ⊆ BF (c i) r,
  { intro i,
    rcases exists_pos_lt_subset_ball (hR0 i) is_closed_closure
      (subset.trans (hVBF i) (inter_subset_left _ _)) with ⟨r, hIoo, hrV⟩,
    exact ⟨r, hIoo, subset_inter hrV (subset.trans (hVBF i) (inter_subset_right _ _))⟩ },
  choose r hlt hrV,
  set f : ι → msmooth_bump_function IF M := λ i, ⟨c i, r i, R i, (hlt i).1, (hlt i).2, hcBFR i⟩,
  refine ⟨⟨ι, _, f, hcs, _, λ x hx, _, λ i, _⟩⟩,
  { simpa only [(f _).support_eq_symm_image] },
  { refine (mem_Union.1 $ hsV hx).imp (λ i hi, _),
    refine mem_nhds_sets_iff.2 ⟨V i, λ x' hx', _, hVo i, hi⟩,
    exact (f i).one_of_dist_le (Bsrc _ $ hVB _ $ subset_closure hx')
      (le_of_lt (hrV i (subset_closure $ mem_image_of_mem _ hx')).1) },
  { calc closure (support (f i)) ⊆ cB (c i) (R i) :
      (f i).closure_support_subset_symm_image_closed_ball
    ... ⊆ U (c i) : hcBR i }
end

/-- Choice of a covering of a manifold by supports of smooth bump functions. -/
def choice [t2_space M] [sigma_compact_space M] (U : M → set M) (hU : ∀ x, U x ∈ 𝓝 x) :
  smooth_bump_covering IE univ U :=
choice_set IE univ is_closed_univ U (λ x hx, hU x)

variables {s : set M} {U : M → set M} (f : smooth_bump_covering IE s U) {IE}

instance : has_coe_to_fun (smooth_bump_covering IE s U) := ⟨_, to_fun⟩

protected lemma locally_finite : locally_finite (λ i, support (f i)) := f.locally_finite'

lemma mem_chart_at_source_of_eq_one {i : f.ι} {x : M} (h : f i x = 1) :
  x ∈ (chart_at H (f i).c).source :=
(f i).support_subset_source $ by simp [h]

lemma mem_ext_chart_at_source_of_eq_one {i : f.ι} {x : M} (h : f i x = 1) :
  x ∈ (ext_chart_at IE (f i).c).source :=
by { rw ext_chart_at_source, exact f.mem_chart_at_source_of_eq_one h }

/-- Index of a bump function such that `f i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : f.ι := (f.eventually_eq_one' x hx).some

lemma eventually_eq_one (x : M) (hx : x ∈ s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
(f.eventually_eq_one' x hx).some_spec

lemma apply_ind (x : M) (hx : x ∈ s) : f (f.ind x hx) x = 1 :=
(f.eventually_eq_one x hx).eq_of_nhds

lemma mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (f $ f.ind x hx) :=
by simp [f.apply_ind x hx]

lemma mem_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (chart_at H (f (f.ind x hx)).c).source :=
f.mem_chart_at_source_of_eq_one (f.apply_ind x hx)

lemma mem_ext_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (ext_chart_at IE (f (f.ind x hx)).c).source :=
f.mem_ext_chart_at_source_of_eq_one (f.apply_ind x hx)

lemma closure_support_subset (i : f.ι) : closure (support $ f i) ⊆ U (f i).c :=
f.closure_support_subset' i

section embedding

instance fintype_ι_of_compact [compact_space M] : fintype f.ι :=
f.locally_finite.fintype_of_compact $ λ i, (f i).nonempty_support

variables [t2_space M] [fintype f.ι]

/-- Smooth embedding of `M` into `(E × ℝ) ^ f.ι`. -/
def embedding_pi_tangent : C^∞⟮IE, M; 𝓘(ℝ, f.ι → (E × ℝ)), f.ι → (E × ℝ)⟯ :=
{ to_fun := λ x i, (f i x • ext_chart_at IE (f i).c x, f i x),
  times_cont_mdiff_to_fun := times_cont_mdiff_pi_space.2 $ λ i,
    ((f i).smooth_smul times_cont_mdiff_on_ext_chart_at).prod_mk_space ((f i).smooth) }

local attribute [simp] lemma embedding_pi_tangent_coe :
  ⇑f.embedding_pi_tangent = λ x i, (f i x • ext_chart_at IE (f i).c x, f i x) :=
rfl

lemma embedding_pi_tangent_inj_on : inj_on f.embedding_pi_tangent s :=
begin
  intros x hx y hy h,
  simp only [embedding_pi_tangent_coe, funext_iff] at h,
  obtain ⟨h₁, h₂⟩ := prod.mk.inj_iff.1 (h (f.ind x hx)),
  rw [f.apply_ind x hx] at h₂,
  rw [← h₂, f.apply_ind x hx, one_smul, one_smul] at h₁,
  have := f.mem_ext_chart_at_source_of_eq_one h₂.symm,
  exact (ext_chart_at IE (f _).c).inj_on (f.mem_ext_chart_at_ind_source x hx) this h₁
end

lemma embedding_pi_tangent_injective (f : smooth_bump_covering IE (univ : set M) U)
  [fintype f.ι] :
  injective f.embedding_pi_tangent :=
injective_iff_inj_on_univ.2 f.embedding_pi_tangent_inj_on

lemma comp_embedding_pi_tangent_mfderiv (x : M) (hx : x ∈ s) :
  ((continuous_linear_map.fst ℝ E ℝ).comp
    (@continuous_linear_map.proj ℝ _ f.ι (λ _, E × ℝ) _ _ (λ _, infer_instance) (f.ind x hx))).comp
      (mfderiv IE 𝓘(ℝ, f.ι → (E × ℝ)) f.embedding_pi_tangent x) =
  mfderiv IE IE (chart_at H (f (f.ind x hx)).c) x :=
begin
  set L := ((continuous_linear_map.fst ℝ E ℝ).comp
    (@continuous_linear_map.proj ℝ _ f.ι (λ _, E × ℝ) _ _ (λ _, infer_instance) (f.ind x hx))),
  have := (L.has_mfderiv_at.comp x (f.embedding_pi_tangent.mdifferentiable_at.has_mfderiv_at)),
  convert has_mfderiv_at_unique this _,
  refine (has_mfderiv_at_ext_chart_at IE (f.mem_chart_at_ind_source x hx)).congr_of_eventually_eq _,
  refine (f.eventually_eq_one x hx).mono (λ y hy, _),
  simp only [embedding_pi_tangent_coe, continuous_linear_map.coe_comp', (∘),
    continuous_linear_map.coe_fst', continuous_linear_map.proj_apply],
  rw [hy, pi.one_apply, one_smul]
end

lemma embedding_pi_tangent_ker_mfderiv (x : M) (hx : x ∈ s) :
  (mfderiv IE 𝓘(ℝ, f.ι → (E × ℝ)) f.embedding_pi_tangent x).ker = ⊥ :=
begin
  apply bot_unique,
  rw [← (mdifferentiable_chart IE (f (f.ind x hx)).c).ker_mfderiv_eq_bot
    (f.mem_chart_at_ind_source x hx), ← comp_embedding_pi_tangent_mfderiv],
  exact linear_map.ker_le_ker_comp _ _
end

lemma embedding_pi_tangent_injective_mfderiv (x : M) (hx : x ∈ s) :
  injective (mfderiv IE 𝓘(ℝ, f.ι → (E × ℝ)) f.embedding_pi_tangent x) :=
linear_map.ker_eq_bot.1 (f.embedding_pi_tangent_ker_mfderiv x hx)

end embedding

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
lemma exists_embedding_findim [t2_space M] {U} (f : smooth_bump_covering IE (univ : set M) U)
  [fintype f.ι] :
  ∃ (n : ℕ) (e : M → euclidean_space ℝ (fin n)), smooth IE 𝓘(ℝ, euclidean_space ℝ (fin n)) e ∧
    injective e ∧ ∀ x : M, injective (mfderiv IE 𝓘(ℝ, euclidean_space ℝ (fin n)) e x) :=
begin
  set F := euclidean_space ℝ (fin $ findim ℝ (f.ι → (E × ℝ))),
  letI : finite_dimensional ℝ (E × ℝ) := by apply_instance,
  set eEF : (f.ι → (E × ℝ)) ≃L[ℝ] F :=
    continuous_linear_equiv.of_findim_eq findim_euclidean_space_fin.symm,
  refine ⟨_, eEF ∘ f.embedding_pi_tangent,
    eEF.to_diffeomorph.smooth.comp f.embedding_pi_tangent.smooth,
    eEF.injective.comp f.embedding_pi_tangent_injective, λ x, _⟩,
  rw [mfderiv_comp _ eEF.differentiable_at.mdifferentiable_at
    f.embedding_pi_tangent.mdifferentiable_at, eEF.mfderiv_eq],
  exact eEF.injective.comp (f.embedding_pi_tangent_injective_mfderiv _ trivial)
end

end smooth_bump_covering

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
lemma exists_embedding_findim_of_compact [t2_space M] [compact_space M] :
  ∃ (n : ℕ) (e : M → euclidean_space ℝ (fin n)), smooth IE 𝓘(ℝ, euclidean_space ℝ (fin n)) e ∧
    injective e ∧ ∀ x : M, injective (mfderiv IE 𝓘(ℝ, euclidean_space ℝ (fin n)) e x) :=
(smooth_bump_covering.choice IE (λ _, univ) (λ x, univ_mem_sets)).exists_embedding_findim
