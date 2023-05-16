import root_system.basic
import linear_algebra.finsupp

open set function

namespace is_root_system

variables {k V : Type*} [linear_ordered_field k] [char_zero k] [add_comm_group V] [module k V]
variables {Φ : set V} (h : is_root_system k Φ)
include h

local postfix `ᘁ`:100 := h.coroot
local notation `ട` := h.symmetry_of_root

@[simp] lemma coroot_symmetry_apply_eq (α β : Φ) (h') :
  ⟨ട α β, h'⟩ᘁ = βᘁ - (βᘁ α) • αᘁ :=
begin
  set γ : Φ := ⟨ട α β, h'⟩,
  have hγ : module.to_pre_symmetry (γ : V) (βᘁ - βᘁ α • αᘁ) = (ട α) * (ട β) * (ട α),
  { ext v,
    simp only [subtype.coe_mk, module.to_pre_symmetry_apply, linear_map.sub_apply,
      linear_map.smul_apply, linear_map.mul_apply],
    -- TODO It should be possibly to fold the `erw` into the `simp only` by sorting out simp-normal
    -- form for various coercions.
    erw [h.symmetry_of_root_apply, h.symmetry_of_root_apply, h.symmetry_of_root_apply,
      h.symmetry_of_root_apply],
    simp only [map_sub, linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul,
      coroot_apply_self_eq_two, smul_smul, mul_sub, sub_mul, sub_smul, smul_sub, mul_two, add_smul,
    mul_comm (βᘁ α) (αᘁ v)],
    abel, },
  have hγ₀ : (γ : V) ≠ 0, { intros contra, apply h.zero_not_mem, rw ← contra, exact γ.property, },
  apply module.eq_dual_of_to_pre_symmetry_image_subseteq hγ₀ h.finite h.span_eq_top, -- f, g implicit
  { exact h.coroot_apply_self_eq_two γ, },
  { exact h.coroot_to_pre_symmetry_subset γ, },
  { simp only [symmetry_of_root_apply, mul_sub, subtype.coe_mk, linear_map.sub_apply, map_sub,
      coroot_apply_self_eq_two, linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul,
      linear_map.smul_apply],
    ring, },
  { rw hγ,
    change ((ട α) ∘ (ട β) ∘ (ട α)) '' Φ ⊆ Φ,
    rw ← comp.assoc,
    simp only [image_comp, h.symmetry_of_root_image_eq], },
end

lemma finite_coroots : (range h.coroot).finite :=
@set.finite_range _ _ h.coroot $ finite_coe_iff.mpr h.finite

/-- An auxiliary result used only to prove `is_root_system.coroot_span_eq_top`.

Note that `is_root_system.to_dual` shows that any root system carries a _canonical_ non-singular
invariant bilinear form. This lemma only exists because we need it to prove the coroots span the
dual space which we use to show `is_root_system.to_dual` is non-singular. -/
lemma exists_to_dual_ker_eq_bot_forall :
  ∃ B : V →ₗ[k] V →ₗ[k] k, B.ker = ⊥ ∧ ∀ v w (α : Φ), B (ട α v) (ട α w) = B v w :=
begin
  haveI := h.finite_dimensional,
  haveI : finite h.weyl_group := h.finite_weyl_group,
  obtain ⟨B, hB₁, hB₂⟩ := module.exists_to_dual_ker_eq_bot h.weyl_group.subtype,
  exact ⟨B, hB₁, λ v w α, hB₂ v w ⟨ട α, h.symmetry_mem_weyl_group α⟩⟩,
end

lemma coroot_eq_zero_only_if_v_eq_zero : ∀ (v : V) (h' : ∀ (α : Φ), h.coroot α v = 0), v = 0 :=
begin
  intros v hv,
  obtain ⟨B, h1, h2⟩ := h.exists_to_dual_ker_eq_bot_forall,
  replace hv : ∀ α, ട α v = v,
  { intro α,
    rw [h.symmetry_of_root_apply, hv, zero_smul, sub_zero], },
  specialize h2 v,
  simp_rw hv at h2,
  replace h2 : ∀ (α : Φ), (B v) ((h.symmetry_of_root α) α) = (B v) α,
  { intros α,
    rw h2, },
  simp only [symmetry_of_root_apply_self_neg, map_neg, set_coe.forall, subtype.coe_mk,
    neg_eq_self_iff] at h2,
  have h3 : ∀ (α : Φ), (B v) α = 0 := λ x, h2 x.1 x.2,
  have h4 : (B v) = 0,
  { ext α,
    change (B v) α = 0,
    have h5 : α ∈ submodule.span k Φ,
    { rw h.span_eq_top,
      exact submodule.mem_top, },
    rw mem_span_set at h5,
    rcases h5 with ⟨c, hc, rfl⟩,
    simp only [linear_map.map_finsupp_sum, linear_map.map_smulₛₗ,
    ring_hom.id_apply, algebra.id.smul_eq_mul],
    refine finset.sum_eq_zero (λ p hp, _),
    dsimp,
    specialize h3 ⟨p, hc (finset.mem_coe.mp hp)⟩,
    simp only [mul_eq_zero],
    exact or.intro_right _ h3, },
  rw linear_map.ker_eq_bot at h1,
  refine h1 _,
  rw linear_map.map_zero,
  exact h4,
end

lemma coroot_span_eq_top : submodule.span k (range h.coroot) = ⊤ :=
begin
  suffices : ∀ (v : V) (h' : ∀ (α : Φ), h.coroot α v = 0), v = 0,
  { contrapose! this,
    rw ← lt_top_iff_ne_top at this,
    obtain ⟨f, hf, hf'⟩ := submodule.exists_dual_map_eq_bot_of_lt_top this,
    haveI := h.finite_dimensional,
    refine ⟨(module.eval_equiv k V).symm f, λ α, _,
      by simpa only [ne.def, linear_equiv.map_eq_zero_iff]⟩,
    simp only [module.apply_eval_equiv_symm_apply, ←submodule.mem_bot k, ←hf', submodule.mem_map],
    refine ⟨h.coroot α, _, rfl⟩,
    apply submodule.subset_span,
    exact mem_range_self α,},
  exact h.coroot_eq_zero_only_if_v_eq_zero,
end

theorem fd {k V : Type*}
  [linear_ordered_field k]
  [char_zero k]
  [add_comm_group V]
  [module k V]
  {Φ : set V}
  (h : is_root_system k Φ)
  (α : ↥Φ)
  [_inst : _root_.finite_dimensional k V] :
  ⇑(module.to_pre_symmetry (h.coroot α)
           ((module.eval_equiv k V) ↑α)) ''
      range h.coroot ⊆
    range h.coroot :=
begin
  simp only [module.to_pre_symmetry_apply, image_subset_iff],
  rintros y ⟨β, rfl⟩,
  simp,
  exact ⟨ട α β, h.symmetry_of_root_apply_mem α β, h.coroot_symmetry_apply_eq α β _⟩,
end

/-- A root system in `V` naturally determines another root system in the dual `V^*`. -/
lemma is_root_system_coroots : is_root_system k $ range h.coroot :=
{ finite := h.finite_coroots,
  span_eq_top := h.coroot_span_eq_top,
  exists_dual :=
    begin
    rintros x ⟨α, rfl⟩,
    refine ⟨module.dual.eval k V α, by simp, _⟩,
    simp only [module.to_pre_symmetry_apply, module.dual.eval_apply, image_subset_iff],
    rintros y ⟨β, rfl⟩,
    simp only [mem_preimage, mem_range, set_coe.exists],
    exact ⟨ട α β, h.symmetry_of_root_apply_mem α β, h.coroot_symmetry_apply_eq α β _⟩,
  end,
  subset_zmultiples :=
  begin
    rintros aux ⟨α, rfl⟩ α' ⟨h₁, h₂⟩ - ⟨-, ⟨β, rfl⟩, rfl⟩,
    have hα : h.coroot α ≠ 0, {
        intro h,
        simp only [h, linear_map.map_zero] at h₁,
        norm_num at h₁,
    },
    haveI := h.finite_dimensional,
    rw module.eq_dual_of_to_pre_symmetry_image_subseteq (hα) h.finite_coroots h.coroot_span_eq_top h₁ h₂ (_ : module.eval_equiv k V α (h.coroot α) = 2) _,
    {
      refine h.subset_zmultiples β β.property (h.coroot β) ⟨h.coroot_apply_self_eq_two β, _⟩ ⟨α, α.property, rfl⟩,
      exact h.symmetry_of_root_image_subset β,
    },
    {
      exact h.coroot_apply_self_eq_two α,
    },
    {
      apply fd,
    },
  end, }

end is_root_system
