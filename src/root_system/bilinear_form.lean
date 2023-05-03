import root_system.dual
import linear_algebra.bilinear_form
import data.set.function
import tactic.field_simp

noncomputable theory

open_locale tensor_product big_operators classical
open set function

namespace is_root_system

-- Need ordering of scalars to have concept of positive definiteness which we will use in proofs
-- below
variables {k V : Type*} [linear_ordered_field k] [char_zero k] [add_comm_group V] [module k V]
variables {Φ : set V} (h : is_root_system k Φ)
include h

local postfix `ᘁ`:100 := h.coroot
local notation `ട` := h.symmetry_of_root

/-- The linear map `V → V⋆` induced by a root system. -/
@[simps] def to_dual : V →ₗ[k] module.dual k V :=
{ to_fun := λ x, ∑ᶠ α, αᘁ x • αᘁ,
  map_add' := λ x y ,
  begin
    ext,
    simp only [linear_map.map_add, map_add, linear_map.add_apply, add_smul],
    rw finsum_add_distrib,
    simp only [linear_map.add_apply],
    { haveI : finite Φ := finite_coe_iff.mpr h.finite,
      apply set.to_finite, },
    { haveI : finite Φ := finite_coe_iff.mpr h.finite,
      apply set.to_finite, },
  end,
  map_smul' :=
  begin
    intros c x,
    ext,
    simp only [linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul,
      linear_map.smul_apply, ←smul_smul],
    rw [← smul_finsum],
    simp only [linear_map.smul_apply, algebra.id.smul_eq_mul],
  end }

lemma to_dual_apply_apply (x y : V) :
  h.to_dual x y = ∑ᶠ α, αᘁ x • αᘁ y :=
begin
 haveI h2 : finite Φ := finite_coe_iff.mpr h.finite,
 have h3 : (support (λ (α : ↥Φ), (αᘁ) x • αᘁ)).finite, by apply set.to_finite,
 change (∑ᶠ (α : Φ), (αᘁ x) • αᘁ) y = _,
 letI : fintype Φ := fintype.of_finite ↥Φ,
 rw finsum_eq_finset_sum_of_support_subset _ (_ : _ ⊆ ↑(finset.univ : finset Φ)),
 rw finsum_eq_finset_sum_of_support_subset _ (_ : _ ⊆ ↑(finset.univ : finset Φ)),
 { simp only [linear_map.coe_fn_sum, fintype.sum_apply, linear_map.smul_apply], },
 { simp only [finset.coe_univ, subset_univ], },
 { simp only [finset.coe_univ, support_subset_iff, mem_univ, implies_true_iff], },
end

/-- The bilinear map on `V` induced by a root system. -/
def to_bilinear_map : V →ₗ[k] V →ₗ[k] k :=
{ to_fun := λ x, h.to_dual x,
  map_add' := λ x y, by { ext, simp only [map_add], },
  map_smul' := λ c x, by { ext, simp only [linear_map.map_smulₛₗ], } }

/-- The bilinear form on `V` induced by a root system. -/
def to_bilin_form : bilin_form k V := h.to_bilinear_map.to_bilin

-- Don't have any zeros or -1s in the matrix only over the real numbers
lemma to_bilin_form_anisotropic : h.to_bilin_form.to_quadratic_form.anisotropic :=
begin
  apply quadratic_form.pos_def.anisotropic,
  intros v hv,
  simp only [to_bilin_form, to_bilinear_map, bilin_form.to_quadratic_form_apply, linear_map.mk_coe],
  change 0 < h.to_dual v v,
  rw to_dual_apply_apply,
  replace hv : ∃ (β : Φ), βᘁ v ≠ 0,
  {
    -- should follow from fact that the coroots span
    sorry, },
  obtain ⟨β, hβ⟩ := hv,
  replace hβ : 0 < (βᘁ v) * (βᘁ v),
  {
    exact mul_self_pos.mpr hβ,},
  sorry,
end

#exit

/-- This corresponds to the bilinear form on V induced by the root system being nonsingular -/
lemma ker_to_dual_eq_bot : h.to_bilin_form.nondegenerate :=
bilin_form.nondegenerate_of_anisotropic h.to_bilin_form_anisotropic


--set_option pp.implicit true
--set_option pp.notation false
-- Bilinear form is dot product, Weyl group is subgroup generated by reflections in the roots,
-- Reflection preserve lengths and angles
-- Therefore bilinear form is preserved
-- Built into some people's definitions, but for us it's a theorem
-- In a Euclidean space we have concept of orthogonality and therefore of reflections
-- Reflections automatically have this property, but we started with weaker assumptions
-- Estimate medium effort.
@[simp] lemma to_bilin_form_symmetry_eq (u : V ≃ₗ[k] V) (hu : u ∈ h.symmetries) (x y : V) :
  h.to_bilin_form (u • x) (u • y) = h.to_bilin_form x y :=
begin
  have hu' : u.symm ∈ h.symmetries := inv_mem_iff.mpr hu,
  have hα : ∀ (α : Φ), u.symm α ∈ Φ,
  { rw [mem_symmetries_iff] at hu',
    intros α,
    apply eq.subset hu',
    exact ⟨α, α.2, rfl⟩, },
  let u' := u.dual_map,
  have h' : ∀ (α : Φ), u.dual_map (h.coroot α) = h.coroot ⟨u.symm α, hα α⟩,
  { intros α,
    rw [coroot_apply_of_mem_symmetries h u.symm hu' α (hα α), linear_equiv.symm_symm], },
  change h.to_dual (u • x) (u • y) = _,
  rw [to_dual_apply_apply],
  dsimp only [has_smul.smul],
  simp_rw [← linear_equiv.dual_map_apply, h'],
  have hbij : set.bij_on u.symm Φ Φ,
  { rw ← linear_equiv.coe_to_equiv,
    suffices : set.bij_on u.symm Φ (u.symm '' Φ),
    { rw (mem_symmetries_iff h u.symm).mp hu' at this, exact this, },
    apply equiv.bij_on_image u.symm.to_equiv, },
  let u_set := set.bij_on.equiv u.symm hbij,
  have hu'' : ∀ (α : Φ), u.symm α = u_set α := λ α, rfl,
  simp_rw hu'',
  simp only [subtype.coe_eta],
  rw @finsum_comp_equiv Φ Φ k _ u_set (λ i, (h.coroot i) x * (h.coroot i) y),
  change ∑ᶠ (i : Φ), (h.coroot i) x • (h.coroot i) y = _,
  rw ← to_dual_apply_apply,
  refl,
end

lemma to_bilin_form_weyl_eq (g : V ≃ₗ[k] V) (hg : g ∈ h.weyl_group) (x y : V) :
  h.to_bilin_form (g • x) (g • y) = h.to_bilin_form x y :=
begin
  have hg' : g ∈ h.symmetries,
  { apply weyl_group_le_symmetries,
    exact hg, },
  apply to_bilin_form_symmetry_eq h g hg',
end


#check @mul_div_cancel
-- Estimate high effort.
lemma to_bilin_form_orthogonal_eq_ker (α : Φ) :
  h.to_bilin_form.orthogonal (k ∙ (α : V)) = (αᘁ).ker :=
begin
  have hα' : h.to_bilin_form α α ≠ 0,
  {
    have h' := h.to_bilin_form_anisotropic,
    contrapose! h',
    rw quadratic_form.not_anisotropic_iff_exists,
    exact ⟨α, h.root_ne_zero α, h'⟩,
  },
  suffices : ∀ (v : V), (h.coroot α) v = 2 * h.to_bilin_form α v / h.to_bilin_form α α,
  { have hb : ∀ (v : V), h.to_bilin_form α v = 0 ↔ (αᘁ) v = 0,
    { intros v,
      -- rw [← bilin_form.mem_orthogonal_iff, ← submodule.mem_bot, ← this],
      -- simp only [submodule.mem_bot, submodule.mem_span_singleton, bilin_form.mem_orthogonal_iff],
      refine ⟨λ hbα, _, λ hbα, _⟩,
      { rw this,
        rw hbα,
        rw mul_zero,
        exact zero_div _, },
      { specialize this v,
        rw hbα at this,
        -- rw eq_div_iff_mul_eq' at this,

        rw [eq_comm, div_eq_zero_iff] at this,
        cases this,
        { simpa only [mul_eq_zero, bit0_eq_zero, one_ne_zero, false_or] using this,},
        { contradiction, },

        -- have hbb : 0 = 2 * (h.to_bilin_form) α v,
        -- {
        --   --rw div_eq_zero_iff att ,
        --   sorry, },
        -- norm_num at hbb,
        -- exact hbb,
      }, },
    ext v,
    rw bilin_form.mem_orthogonal_iff,
    rw linear_map.mem_ker,
    simp_rw [bilin_form.is_ortho_def],
    refine ⟨λ h, _, λ h, _⟩,
    { specialize h (α : V),
      rw hb at h,
      rw h,
      rw submodule.mem_span,
      simp only [singleton_subset_iff, set_like.mem_coe, imp_self, forall_const], },
    { intros n hn,
      rw submodule.mem_span_singleton at hn,
      rcases hn with ⟨z, rfl⟩,
      simp only [bilin_form.smul_left, mul_eq_zero],
      refine or.intro_right _ _,
      rw hb,
      exact h, }, },
  intro v,
  let u := h.symmetry_of_root α,
  have hu : u ∈ h.symmetries,
  { simp only [mem_symmetries_iff, symmetry_of_root_image_eq], },
  have hu' : h.to_bilin_form α v =
     (h.coroot α) v * h.to_bilin_form α α - (h.to_bilin_form α v),
  {
    let n := h.to_bilin_form α v,
    -- change n = _,
    conv { to_lhs,
      rw ← h.to_bilin_form_symmetry_eq u hu α v,
      dsimp [(•)],
      rw h.symmetry_of_root_apply_self_neg α,
      rw h.symmetry_of_root_apply,
      rw bilin_form.sub_right,
      rw bilin_form.neg_left,
      rw bilin_form.smul_right,
      rw bilin_form.neg_left,
      simp only [mul_neg, neg_sub_neg, sub_sub_cancel], },
  },
  rw eq_sub_iff_add_eq at hu',
  rw ← two_mul at hu',
  rw hu',
  rw mul_div_cancel _ hα',
end

end is_root_system
