import linear_algebra.contraction
import group_theory.order_of_element
import linear_algebra.bilinear_form
import linear_algebra.quadratic_form.basic

noncomputable theory

open_locale tensor_product big_operators classical
open set function

@[simp] lemma module.apply_eval_equiv_symm_apply
  {k V : Type*} [field k] [add_comm_group V] [module k V] [finite_dimensional k V]
  (f : module.dual k V) (v : module.dual k $ module.dual k V) :
  f ((module.eval_equiv k V).symm v) = v f :=
begin
  set w := (module.eval_equiv k V).symm v,
  have hw : v = module.eval_equiv k V w := (linear_equiv.apply_symm_apply _ _).symm,
  rw hw,
  refl,
end

@[simp] lemma module.coe_End_one {k V : Type*} [semiring k] [add_comm_monoid V] [module k V] :
  ⇑(1 : (module.End k V)ˣ) = id :=
rfl

attribute [protected] module.finite

namespace module

variables {k V : Type*} [comm_ring k] [add_comm_group V] [module k V]

/-- Given a vector `x` and a linear form `f`, this is the map `y ↦ y - (f y) • x`, bundled as a
linear endomorphism.

When `f x = 2`, it is involutive and sends `x ↦ - x`. See also `module.to_symmetry`. -/
def to_pre_symmetry (x : V) (f : dual k V) : End k V :=
linear_map.id - dual_tensor_hom k V V (f ⊗ₜ x)

@[simp] lemma to_pre_symmetry_apply (x y : V) (f : dual k V) :
  to_pre_symmetry x f y = y - (f y) • x :=
by simp [to_pre_symmetry]

lemma to_pre_symmetry_apply_self {x : V} {f : dual k V} (h : f x = 2) :
  to_pre_symmetry x f x = - x :=
by { rw [to_pre_symmetry_apply, h, ← one_smul k x, smul_smul, ← sub_smul], norm_num, }

lemma to_pre_symmetry_sq {x : V} {f : dual k V} (h : f x = 2) :
  (to_pre_symmetry x f)^2 = linear_map.id :=
begin
  ext β,
  rw [linear_map.pow_apply, iterate_succ, iterate_one, comp_app],
  nth_rewrite 1 to_pre_symmetry_apply,
  rw [map_sub, map_smul, to_pre_symmetry_apply_self h, to_pre_symmetry_apply,
    smul_neg, sub_neg_eq_add, sub_add_cancel, linear_map.id_apply],
end

/-- Given a vector `x` and a linear form `f` such that `f x = 2`, this is the map
`y ↦ y - (f y) • x`, bundled as a linear automorphism. -/
def to_symmetry {x : V} {f : dual k V} (h : f x = 2) : units (End k V) :=
⟨to_pre_symmetry x f, to_pre_symmetry x f, to_pre_symmetry_sq h, to_pre_symmetry_sq h⟩

@[simp] lemma to_symmetry_inv {x : V} {f : dual k V} (h : f x = 2) :
  (to_symmetry h)⁻¹ = to_symmetry h :=
begin
  rw [← mul_left_inj (to_symmetry h), mul_left_inv, ← sq, eq_comm, units.ext_iff],
  exact to_pre_symmetry_sq h,
end

@[simp] lemma eq_zero_or_zero_of_dual_tensor_hom_tmul_eq_zero
  {f : dual k V} {x : V} [no_zero_smul_divisors k V] :
  dual_tensor_hom k V V (f ⊗ₜ x) = 0 ↔ f = 0 ∨ x = 0  :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases eq_or_ne x 0 with rfl | hx, { simp, },
    left,
    ext v,
    simp only [linear_map.zero_apply],
    replace h : f v • x = 0 :=
      by simpa only [dual_tensor_hom_apply, linear_map.zero_apply] using linear_map.congr_fun h v,
    rw smul_eq_zero at h,
    tauto, },
  { rcases h with rfl | rfl; simp, },
end

-- Like proof of finiteness of weyl group
lemma unit.is_of_fin_order_of_finite_of_span_eq_top_of_image_subseteq
  {Φ : set V} (hΦ₁ : Φ.finite) (hΦ₂ : submodule.span k Φ = ⊤)
  {u : (End k V)ˣ} (hu : u '' Φ ⊆ Φ) : is_of_fin_order u :=
sorry

/-- Uniqueness lemma from page 25 of Serre's "Complex semisimple Lie algebras". -/
lemma eq_dual_of_to_pre_symmetry_image_subseteq [char_zero k] [no_zero_smul_divisors k V]
  {x : V} (hx : x ≠ 0)
  {Φ : set V} (hΦ₁ : Φ.finite) (hΦ₂ : submodule.span k Φ = ⊤)
  {f g : dual k V} (hf₁ : f x = 2) (hf₂ : to_pre_symmetry x f '' Φ ⊆ Φ)
                   (hg₁ : g x = 2) (hg₂ : to_pre_symmetry x g '' Φ ⊆ Φ) :
  f = g :=
begin
  let u := to_symmetry hg₁ * to_symmetry hf₁,
  suffices : is_of_fin_order u,
  { have hu : ↑u = linear_map.id + dual_tensor_hom k V V ((f - g) ⊗ₜ x),
    { ext y,
      simp only [to_symmetry, hg₁, units.coe_mul, units.coe_mk, linear_map.mul_apply, id.def,
        to_pre_symmetry_apply, map_sub, linear_map.map_smulₛₗ, ring_hom.id_apply, sub_smul, two_smul,
        linear_map.add_apply, linear_map.id_coe, dual_tensor_hom_apply, linear_map.sub_apply,
        sub_add_cancel', smul_neg, sub_neg_eq_add],
      abel, },
    replace hu : ∀ (n : ℕ), ↑(u^n) = linear_map.id + (n : k) • dual_tensor_hom k V V ((f - g) ⊗ₜ x),
    { intros n,
      induction n with n ih, { simpa, },
      have aux : (dual_tensor_hom k V V ((f - g) ⊗ₜ[k] x)).comp
        ((n : k) • dual_tensor_hom k V V ((f - g) ⊗ₜ[k] x)) = 0, { ext v, simp [hf₁, hg₁], },
      rw [pow_succ, units.coe_mul, ih, hu, add_mul, mul_add, mul_add],
      simp only [linear_map.mul_eq_comp, linear_map.id_comp, linear_map.comp_id, nat.cast_succ,
        aux, add_zero, add_smul, one_smul, add_assoc], },
    obtain ⟨n, hn₀, hn₁⟩ := (is_of_fin_order_iff_pow_eq_one u).mp this,
    specialize hu n,
    replace hn₁ : ↑(u ^ n) = linear_map.id := units.ext_iff.mp hn₁,
    simpa only [hn₁, smul_eq_zero, nat.cast_eq_zero, hn₀.ne', false_or, or_false, hx,
      eq_zero_or_zero_of_dual_tensor_hom_tmul_eq_zero, sub_eq_zero, self_eq_add_right] using hu, },
  suffices : u '' Φ ⊆ Φ,
  { exact unit.is_of_fin_order_of_finite_of_span_eq_top_of_image_subseteq hΦ₁ hΦ₂ this, },
  change (to_pre_symmetry x g ∘ to_pre_symmetry x f '' Φ) ⊆ Φ,
  rw [image_comp],
  exact (monotone_image hf₂).trans hg₂,
end

@[simp] lemma subsingleton_dual_iff {k V : Type*} [field k] [add_comm_group V] [module k V] :
  subsingleton (dual k V) ↔ subsingleton V :=
begin
  refine ⟨λ h, ⟨λ v w, _⟩, λ h, ⟨λ f g, _⟩⟩,
  { rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff k (v - w)],
    intros f,
    simp [@subsingleton.elim _ h f 0], },
  { ext v,
    simp [@subsingleton.elim _ h v 0], },
end

@[simp] lemma nontrivial_dual_iff {k V : Type*} [field k] [add_comm_group V] [module k V] :
  nontrivial (dual k V) ↔ nontrivial V :=
by rw [← not_iff_not, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton,
  subsingleton_dual_iff]

-- May or may not need this.
@[simp] lemma _root_.quadratic_form.to_quadratic_form_polar_bilin (Q : quadratic_form k V) :
  Q.polar_bilin.to_quadratic_form = (2 : k) • Q :=
by { ext, simp, }

-- May or may not need this.
@[simp] lemma _root_.bilin_form.to_quadratic_form.polar_bilin
  {B : bilin_form k V} (h : B.is_symm) :
  B.to_quadratic_form.polar_bilin = (2 : k) • B :=
begin
  ext v w,
  erw [quadratic_form.polar_bilin_apply, bilin_form.smul_apply, bilin_form.polar_to_quadratic_form,
    h.eq w v, two_smul],
end

/-- Given a representation of a finite group on a space carrying a bilinear form, we can take
the average to obtain an invariant bilinear form.

The API for `finsum` should be expanded to interact well with `finite`. This would make the proofs
below trivial. -/
def average_bilinear {G : Type*} [group G] [finite G]
  (ρ : G →* (End k V)ˣ) (B : V →ₗ[k] dual k V) :
  V →ₗ[k] dual k V :=
{ to_fun := λ v, ∑ᶠ g, (B ((ρ g) • v)).comp (ρ g : V →ₗ[k] V),
  map_add' := λ v w,
  begin
    rw ← finsum_add_distrib _,
    { simp only [smul_add, map_add, linear_map.add_comp], },
    { apply set.to_finite, },
    { apply set.to_finite, },
  end,
  map_smul' := λ t v,
  begin
    haveI : fintype G := fintype.of_finite G,
    simp only [finsum_eq_sum_of_fintype, ring_hom.id_apply, finset.smul_sum],
    congr,
    ext g w,
    suffices : ρ g • t • v = t • ρ g • v,
    { simp only [linear_map.comp_apply, linear_map.smul_apply, map_smul, this], },
    exact linear_map.map_smul ↑(ρ g) t v,
  end, }

lemma average_bilinear_apply_apply {G : Type*} [group G] [finite G]
  (ρ : G →* (End k V)ˣ) (B : V →ₗ[k] dual k V) (v w : V) :
  average_bilinear ρ B v w = ∑ᶠ g, B ((ρ g) • v) ((ρ g) • w) :=
begin
  haveI : fintype G := fintype.of_finite G,
  simpa only [average_bilinear, linear_map.coe_mk, finsum_eq_sum_of_fintype, linear_map.coe_fn_sum,
    linear_map.coe_comp, finset.sum_apply, comp_app],
end

@[simp] lemma _root_.quadratic_form.group_action.pos_def_iff
  {k V : Type*} [linear_ordered_field k] [add_comm_group V] [module k V]
  (Q : quadratic_form k V) (g : (End k V)ˣ) :
  (Q.comp (g : V →ₗ[k] V)).pos_def ↔ Q.pos_def :=
sorry

-- Can avoid proving this lemma if we delete `average_bilinear` and just use
-- `∑ᶠ g, B.to_bilin.to_quadratic_form.group_action (ρ g)` instead
lemma average_bilinear_eq_sum {G : Type*} [group G] [finite G]
  (ρ : G →* (End k V)ˣ) (B : V →ₗ[k] dual k V) :
  (average_bilinear ρ B).to_bilin.to_quadratic_form =
  ∑ᶠ g, B.to_bilin.to_quadratic_form.comp (ρ g : V →ₗ[k] V) :=
begin
  ext v,
  haveI : fintype G := fintype.of_finite G,
  simp only [average_bilinear, linear_map.coe_mk, finsum_eq_sum_of_fintype, linear_map.coe_fn_sum,
    linear_map.coe_comp, finset.sum_apply, comp_app, bilin_form.to_quadratic_form_apply,
    quadratic_form.sum_apply, quadratic_form.comp_apply],
  change (∑ g, (B (ρ g • v)).comp ↑(ρ g)) v = ∑ g, B (ρ g v) (ρ g v), -- TODO Should be via `simp`
  simp only [linear_map.coe_fn_sum, finset.sum_apply, linear_map.coe_comp, comp_app],
  refl, -- TODO Should be via `simp`
end

@[simp] lemma average_bilinear_smul_smul {G : Type*} [group G] [finite G]
  (ρ : G →* (End k V)ˣ) (B : V →ₗ[k] dual k V) (v w : V) (g : G) :
  average_bilinear ρ B ((ρ g) • v) ((ρ g) • w) = average_bilinear ρ B v w :=
begin
  simp only [average_bilinear_apply_apply, smul_smul, ← map_mul],
  let b : G → k := λ g', B ((ρ g') • v) ((ρ g') • w),
  let e : G ≃ G := equiv.mul_right g,
  change ∑ᶠ g', (b ∘ e) g' = ∑ᶠ g', b g',
  exact finsum_comp_equiv e,
end

-- A better version of `basis.to_dual_total_left` which we'll need.
@[simp] lemma _root_.basis.to_dual_total_left'
  {R M ι : Type*} [comm_semiring R] [add_comm_monoid M] [module R M] [decidable_eq ι]
  (b : basis ι R M) (f : ι →₀ R) :
  (b.to_dual ((finsupp.total ι M R b) f)) ∘ b = f :=
by { ext, simp, }

lemma _root_.basis.to_dual_pos_def {k V ι : Type*}
  [linear_ordered_field k] [add_comm_group V] [module k V] (b : basis ι k V) :
  b.to_dual.to_bilin.to_quadratic_form.pos_def :=
begin
  intros v hv,
  simp only [bilin_form.to_quadratic_form_apply],
  change 0 < b.to_dual v v, -- TODO Should be via `simp`.
  replace hv : (b.repr v).support.nonempty, { contrapose! hv, simpa using hv, },
  rw [←b.total_repr v, finsupp.apply_total, b.to_dual_total_left', finsupp.total_apply],
  apply finset.sum_pos,
  rintros i hi,
  simp only [finsupp.mem_support_iff] at hi,
  simp only [algebra.id.smul_eq_mul, mul_self_pos, ne.def],
  exact hi,
  exact hv,
end

lemma _root_.quadratic_form.pos_def.sum {k V ι : Type*} [finite ι] [nonempty ι]
  [linear_ordered_field k] [add_comm_group V] [module k V] (q : ι → quadratic_form k V)
  (hq : ∀ i, (q i).pos_def) :
  (∑ᶠ i, q i).pos_def :=
begin
  haveI : fintype ι := fintype.of_finite ι,
  simp only [finsum_eq_sum_of_fintype],
  -- use `finset.sum_induction_nonempty`
  refine finset.sum_induction_nonempty _ _ _ _ _,
  { intros a b ha hb,
    exact quadratic_form.pos_def.add _ _ ha hb, },
  { exact finset.univ_nonempty, },
  { intros i hi,
    exact hq i, },
end

lemma _root_.linear_map.to_bilin.pos_def.ker_eq_bot {k V : Type*}
  [linear_ordered_field k] [add_comm_group V] [module k V] (b : V →ₗ[k] dual k V)
  (hb : b.to_bilin.to_quadratic_form.pos_def) :
  b.ker = ⊥ :=
begin
  ext v,
  simp only [linear_map.mem_ker, submodule.mem_bot],
  refine ⟨λ hv, _, λ hv, _⟩,
  { rw ← hb.anisotropic.eq_zero_iff,
    simp only [bilin_form.to_quadratic_form_apply],
    change b v v = 0, -- TODO Should be via `simp`
    rw hv,
    simp, },
  { rw hv,
    simp, },
end

/-- The assumption `linear_ordered_field` is stronger than necessary but enables an easy proof
by just taking the average of a positive definite bilinear form. -/
lemma exists_to_dual_ker_eq_bot {k V G : Type*}
  [linear_ordered_field k] [add_comm_group V] [module k V] [finite_dimensional k V]
  [group G] [finite G]
  (ρ : G →* (End k V)ˣ) :
  ∃ B : V →ₗ[k] dual k V, B.ker = ⊥ ∧ ∀ v w (g : G), B ((ρ g) • v) ((ρ g) • w) = B v w :=
begin
  obtain ⟨s, ⟨b⟩⟩ := basis.exists_basis k V,
  refine ⟨average_bilinear ρ b.to_dual, _, λ v w g, by simp only [average_bilinear_smul_smul]⟩,
  apply linear_map.to_bilin.pos_def.ker_eq_bot,
  rw average_bilinear_eq_sum,
  apply quadratic_form.pos_def.sum,
  intros g,
  rw quadratic_form.group_action.pos_def_iff,
  convert b.to_dual_pos_def,
  /- Possible alternative approach if seek to drop `average_bilinear`:
  let Q : quadratic_form k V := ∑ᶠ g, b.to_dual.to_bilin.to_quadratic_form.comp (ρ g : V →ₗ[k] V),
  refine ⟨Q.polar_bilin.to_lin, _, λ v w g, _⟩,
  { apply linear_map.to_bilin.pos_def.ker_eq_bot,
    change Q.polar_bilin.to_quadratic_form.pos_def, -- TODO Should be via `simp`
    simp only [quadratic_form.to_quadratic_form_polar_bilin],
    refine quadratic_form.pos_def.smul _ (two_pos : 0 < (2 : k)),
    apply quadratic_form.pos_def.sum,
    intros g,
    rw quadratic_form.group_action.pos_def_iff,
    convert b.to_dual_pos_def, },
  { change Q.polar_bilin (ρ g v) (ρ g w) = Q.polar_bilin v w, -- TODO Should be via `simp`
    sorry, },
  -/
end

end module

namespace submodule

variables {k V : Type*} [field k] [add_comm_group V] [module k V] {p : submodule k V}

-- For any proper submodule there exists a non-zero linear form vanishing on it
lemma exists_dual_map_eq_bot_of_lt_top (hp : p < ⊤) : ∃ f : module.dual k V, f ≠ 0 ∧ p.map f = ⊥ :=
begin
  replace hp : nontrivial (module.dual k $ V ⧸ p) :=
    module.nontrivial_dual_iff.mpr (quotient.nontrivial_of_lt_top p hp),
  obtain ⟨f, g, h⟩ := hp,
  replace h : f - g ≠ 0 := sub_ne_zero.mpr h,
  refine ⟨(f - g).comp p.mkq, _, by simp [map_comp]⟩,
  contrapose! h,
  refine p.quot_hom_ext (λ v, _),
  change (f - g).comp p.mkq v = _,
  simp [h],
end

end submodule
