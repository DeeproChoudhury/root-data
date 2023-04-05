import root_system.dual
import linear_algebra.bilinear_form

noncomputable theory

open_locale tensor_product big_operators classical
open set function

namespace is_root_system

variables {k V : Type*} [field k] [char_zero k] [add_comm_group V] [module k V]
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

/-- This corresponds to the bilinear form on V induced by the root system being nonsingular -/
lemma ker_to_dual_eq_bot : h.to_dual.ker = ⊥ :=
sorry


-- Bilinear form is dot product, Weyl group is subgroup generated by reflections in the roots,
-- Reflection preserve lengths and angles
-- Therefore bilinear form is preserved
-- Built into some people's definitions, but for us it's a theorem
-- In a Euclidean space we have concept of orthogonality and therefore of reflections
-- Reflections automatically have this property, but we started with weaker assumptions
-- Estimate medium effort.
@[simp] lemma to_bilin_form_weyl_eq (g : h.weyl_group) (x y : V) :
  h.to_bilin_form (g • x) (g • y) = h.to_bilin_form x y :=
begin
  sorry,
end

-- Estimate high effort.
lemma to_bilin_form_orthogonal_eq_ker (α : Φ) :
  h.to_bilin_form.orthogonal (k ∙ (α : V)) = (αᘁ).ker :=
begin
  apply le_antisymm,
  { intros x hx,
    simp only [linear_map.mem_ker],
    cases h.exists_int_coroot_apply_eq α _ with n hn,
    sorry,
    assumption, },
  { intros x hx,
    simp only [linear_map.mem_ker] at hx,
    sorry, }
    -- have h1 := h.to_bilin_form_apply_apply α _ _,

    -- simp only [smul_eq_mul, mul_sum, sum_smul],
    -- refine sum_mem _ (λ β hb, _),
    -- rw [← mul_smul, ← mul_smul, ← mul_smul, ← mul_smul],
    -- refine mul_mem _ _ _ _,
    -- { exact h.coroot_apply_mem_zmultiples_2 α β },
    -- { exact h.coroot_apply_mem_zmultiples_2 α x },
    -- { exact h.coroot_apply_mem_zmultiples_2 β x },
    -- { exact h.coroot_apply_mem_zmultiples_2 β α }, },
end

end is_root_system