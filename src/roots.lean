import linear_algebra.contraction
import linear_algebra.bilinear_form
import group_theory.order_of_element

noncomputable theory

open_locale tensor_product big_operators classical
open set function

-- This may already exist in some form in Mathlib.
lemma equiv.symm_apply_mem_of_forall_mem_finite {α : Type*} (e : α ≃ α) {s : set α}
  (h_mem : ∀ x : s, e x ∈ s) (h_fin : s.finite) (x : s) :
  e.symm (x : α) ∈ s :=
begin
  haveI : fintype s := finite.fintype h_fin,
  let f : s → s := λ x, ⟨e x, h_mem x⟩,
  have h_inj : injective f, { rintros ⟨a, ha⟩ ⟨b, hb⟩ hab, simpa using hab, },
  have h_surj : surjective f :=
    ((fintype.bijective_iff_injective_and_card f).mpr ⟨h_inj, rfl⟩).2,
  obtain ⟨y, rfl⟩ := h_surj x,
  change e.symm (e y) ∈ s,
  simp,
end

lemma nat.eq_one_or_two_or_four_of_div_four {n : ℕ} (h : n ∣ 4) : n = 1 ∨ n = 2 ∨ n = 4 :=
begin
  have h₁ := nat.le_of_dvd four_pos h,
  interval_cases n with h;
  revert h;
  dec_trivial,
end

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

lemma unit.is_of_fin_order_of_finite_of_span_eq_top_of_image_subseteq
  {Φ : set V} (hΦ₁ : Φ.finite) (hΦ₂ : submodule.span k Φ = ⊤)
  {u : (End k V)ˣ} (hu : u '' Φ ⊆ Φ) : is_of_fin_order u :=
begin
  sorry,
end

/-- Serre's uniqueness lemma from page 25 of "Complex semisimple Lie algebras". -/
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

end module

section root_systems

/-- A crystallographic root system (possibly non-reduced). -/
@[protect_proj]
class is_root_system (k : Type*) {V : Type*} [comm_ring k] [char_zero k] [add_comm_group V] [module k V]
(Φ : set V) : Prop :=
(finite : Φ.finite)
(span_eq_top : submodule.span k Φ = ⊤)
(exists_dual : ∀ α ∈ Φ, ∃ f : module.dual k V, f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ)
(subset_zmultiples : ∀ (α ∈ Φ) (f : module.dual k V),
  f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ → f '' Φ ⊆ add_subgroup.zmultiples (1 : k))
/-image of phi under the map f is a subset copy of the integers that live in k -/

/-- A reduced, crystallographic root system. -/
structure is_reduced_root_system (k : Type*) {V : Type*} [comm_ring k] [char_zero k] [add_comm_group V] [module k V]
(Φ : set V) extends is_root_system k Φ : Prop :=
(two_smul_not_mem : ∀ α ∈ Φ, 2 • α ∉ Φ)

namespace is_root_system

structure is_base {k V ι : Type*} [linear_ordered_field k] [add_comm_group V] [module k V]
  {Φ : set V} (h : is_root_system k Φ) (b : basis ι k V) : Prop :=
(subset : range (b : ι → V) ⊆ Φ)
(is_integral : ∀ (α ∈ Φ) i, b.coord i α ∈ add_subgroup.zmultiples (1 : k))
(same_sign : ∀ (α ∈ Φ), (∀ i, 0 ≤ b.coord i α) ∨ (∀ i, b.coord i α ≤ 0))

section field

variables {k V : Type*} [field k] [char_zero k] [add_comm_group V] [module k V]

variables {Φ : set V} (h : is_root_system k Φ)
include h

/-- The coroot of a root.

Note that although this uses `classical.some`, the choice is unique (see Serre's lemma). -/
def coroot (α : Φ) : module.dual k V := classical.some $ h.exists_dual _ α.property

local postfix `ᘁ`:100 := h.coroot -- TODO Use more widely

@[simp] lemma coroot_apply_self_eq_two (α : Φ) :
  αᘁ α = 2 :=
(classical.some_spec (h.exists_dual _ α.property)).1

@[simp] lemma coroot_to_pre_symmetry_subset (α : Φ) :
  module.to_pre_symmetry (α : V) (αᘁ) '' Φ ⊆ Φ :=
(classical.some_spec (h.exists_dual _ α.property)).2

lemma zero_not_mem : (0 : V) ∉ Φ :=
λ contra, by simpa using h.coroot_apply_self_eq_two ⟨0, contra⟩

/-- The symmetry associated to a root. -/
def symmetry_of_root (α : Φ) : units (module.End k V) :=
module.to_symmetry $ h.coroot_apply_self_eq_two α

local notation `ട` := h.symmetry_of_root -- TODO Use more widely

lemma symmetry_of_root_apply (α : Φ) (v : V) :
  ട α v = v - αᘁ v • α :=
module.to_pre_symmetry_apply (α : V) v (αᘁ)

@[simp] lemma symmetry_of_root_apply_self_neg (α : Φ) :
  ട α α = - α :=
module.to_pre_symmetry_apply_self $ h.coroot_apply_self_eq_two α

@[simp] lemma symmetry_of_root_sq (α : Φ) : (ട α)^2 = 1 :=
units.ext $ module.to_pre_symmetry_sq $ coroot_apply_self_eq_two h α

protected lemma finite_dimensional : finite_dimensional k V :=
⟨⟨h.finite.to_finset, by simpa only [finite.coe_to_finset] using h.span_eq_top⟩⟩

lemma symmetry_of_root_image_subset (α : Φ) :
  ട α '' Φ ⊆ Φ :=
(classical.some_spec (h.exists_dual _ α.property)).2

@[simp] lemma symmetry_of_root_image_eq (α : Φ) :
  ട α '' Φ = Φ :=
begin
  refine subset_antisymm (h.symmetry_of_root_image_subset α) _,
  have : Φ = ((ട α) ∘ (ട α)) '' Φ, { change Φ = ⇑((ട α)^2) '' Φ, simp, },
  conv_lhs { rw [this, image_comp], },
  mono,
  exact h.symmetry_of_root_image_subset α,
end

@[simp] lemma symmetry_of_root_apply_mem (α β : Φ) : ട α β ∈ Φ :=
begin
  apply h.symmetry_of_root_image_subset α,
  simp only [mem_image],
  exact ⟨ β, β.property, rfl⟩,
end

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
  apply module.eq_dual_of_to_pre_symmetry_image_subseteq hγ₀ h.finite h.span_eq_top,
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

/-- A root system in `V` naturally determines another root system in the dual `V^*`. -/
lemma is_root_system_coroots : is_root_system k $ range h.coroot :=
{ finite := @set.finite_range _ _ h.coroot $ finite_coe_iff.mpr h.finite,
  span_eq_top :=
  begin
    rw eq_top_iff,
    intros x hx,
    obtain ⟨α, rfl⟩ := hx,
    sorry,
  end,
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
    refine h.subset_zmultiples _ β.property (βᘁ) ⟨_, _⟩ ⟨α, α.property, _⟩,
    { simp only [subtype.val_eq_coe, coroot_apply_self_eq_two], },
    { exact h.coroot_to_pre_symmetry_subset β, },
    { haveI := h.finite_dimensional,
      suffices : (α : V) = (module.eval_equiv k V).symm α', { simp [this], },
      rw linear_equiv.eq_symm_apply,
      unfold module.eval_equiv,
      ext z,
      rw [linear_equiv.of_bijective_apply, module.dual.eval_apply],


      sorry, },
  end, }

@[simp] lemma neg_mem (α : Φ) : - (α : V) ∈ Φ :=
begin
  have := (image_subset_iff.mp $ h.symmetry_of_root_image_subset α) α.property,
  simpa only [subtype.val_eq_coe, mem_preimage, symmetry_of_root_apply_self_neg] using this,
end

@[simp] lemma coroot_image_subset_zmultiples (α : Φ) :
  αᘁ '' Φ ⊆ add_subgroup.zmultiples (1 : k) :=
h.subset_zmultiples α α.property (αᘁ)
  ⟨h.coroot_apply_self_eq_two α, h.symmetry_of_root_image_subset α⟩

@[simp] lemma coroot_apply_mem_zmultiples (α β : Φ) :
  αᘁ β ∈ add_subgroup.zmultiples (1 : k) :=
begin
  have := (image_subset_iff.mp $ h.coroot_image_subset_zmultiples α) β.property,
  simpa using this,
end

@[simp] lemma coroot_apply_mem_zmultiples_2 (α β : Φ) :
  ∃ a : ℤ, αᘁ β = a :=
begin
  have hr := h.coroot_apply_mem_zmultiples α β,
  rw add_subgroup.mem_zmultiples_iff at hr,
  simp only [int.smul_one_eq_coe] at hr,
  obtain ⟨a, ha⟩ := hr,
  exact ⟨a, ha.symm⟩,
end

lemma exists_int_coroot_apply_eq (α β : Φ) :
  ∃ (n : ℤ), αᘁ β = n :=
begin
  obtain ⟨n, hn⟩ := add_subgroup.mem_zmultiples_iff.mp (h.coroot_apply_mem_zmultiples α β),
  rw ← hn,
  exact ⟨n, by simp⟩,
end

/-- The Weyl group of a root system. -/
-- reflections are invertible endomorphisms and sit in the endomorphism ring
-- i.e. they are all units in the automorphism group
def weyl_group : subgroup $ (module.End k V)ˣ := subgroup.closure $ range h.symmetry_of_root

-- w acts on α and sends roots to roots (acts on roots)
-- w acting on α gives a root, not a random vector
lemma weyl_group_apply_root_mem (w : h.weyl_group) (α : Φ) : w • (α : V) ∈ Φ :=
begin
  obtain ⟨w, hw⟩ := w,
  change w • (α : V) ∈ Φ,
  revert α,
  have : ∀ (g : (module.End k V)ˣ), g ∈ range h.symmetry_of_root → ∀ (α : Φ), g • (α : V) ∈ Φ,
  { rintros - ⟨β, rfl⟩ α, exact h.symmetry_of_root_image_subset β ⟨α, α.property, rfl⟩, },
  -- Look up what this means
  refine subgroup.closure_induction hw this _ (λ g₁ g₂ hg₁ hg₂ α, _) (λ g hg α, _),
  { simp, },
  { rw mul_smul, exact hg₁ ⟨_, hg₂ α⟩, },
  { let e : V ≃ V := ⟨λ x, g • x, λ x, g⁻¹ • x, λ x, by simp, λ x, by simp⟩,
    exact e.symm_apply_mem_of_forall_mem_finite hg h.finite α, },
end

@[simps]
def weyl_group_to_perm (w : h.weyl_group) : equiv.perm Φ :=
{ to_fun := λ α, ⟨w • (α : V), h.weyl_group_apply_root_mem w α⟩,
  inv_fun := λ α, ⟨w⁻¹ • (α : V), h.weyl_group_apply_root_mem w⁻¹ α⟩,
  left_inv := λ α, by simp,
  right_inv := λ α, by simp, }

@[simps]
def weyl_group_to_perm' : h.weyl_group →* equiv.perm Φ :=
{ to_fun := h.weyl_group_to_perm,
  map_one' := begin
   ext,
   simp [weyl_group_to_perm],
  end,
  map_mul' := begin
  intros α β,
  ext,
  simp [weyl_group_to_perm, mul_smul],
  end, }

lemma injective_weyl_group_to_perm : injective h.weyl_group_to_perm' :=
begin
  rw ←monoid_hom.ker_eq_bot_iff, -- Injective is the same as ker = ⊥
  rw eq_bot_iff,
  intros w hw, -- Let w ∈ ker f
  rw subgroup.mem_bot, -- w ∈ ⊥ ↔ w = 1
  rw monoid_hom.mem_ker at hw, -- x ∈ ker f ↔ f x = 1
  have hw' := fun_like.congr_fun hw, --Functions are equal if that agree for all values
  change ∀ x, _ = x at hw',
  ext v,
  change w v = v,
  have := fun_like.congr_fun hw,
  simp only [weyl_group_to_perm'_apply, equiv.perm.coe_one, id.def, set_coe.forall] at this,
  have mem1: v ∈ submodule.span k Φ,
  { rw h.span_eq_top,
  trivial, },
  apply submodule.span_induction mem1,
  { intros x hx,
    specialize hw' ⟨x, hx⟩,
    dsimp [weyl_group_to_perm, (•)] at hw',
    simp at hw',
    exact hw', },
  { exact linear_map.map_zero _, },
  { intros x y hx hy,
    erw linear_map.map_add,
    change w x + w y = x + y,
    rw [hx, hy], },
  { intros t x hx,
    erw linear_map.map_smul,
    change t • w x = t • x,
    rw hx, },
end

lemma finite_weyl_group : finite h.weyl_group :=
begin
  suffices : finite (equiv.perm Φ),
  { haveI := this,
    exact finite.of_injective _ h.injective_weyl_group_to_perm, },
  haveI : finite Φ := finite_coe_iff.mpr h.finite,
  exact equiv.finite_left,
end

/- Roots span the space and roots are finite so each root symmetry just permutes the roots. Therefore
the Wyel group is a subgroup of the symmetry group
subgroups closure induction-/

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

omit h
theorem foo {k : Type u_1} {V : Type u_2} (n m : ℤ)
  [field k]
  [char_zero k]
  [add_comm_group V]
  [module k V]
  {Φ : set V}
  (hr : is_reduced_root_system k Φ)
  (x : V)
  (hx : x ∈ Φ)
  (t : k)
  (ht : t • x ∈ Φ)
  (ht₀ : t ≠ 0)
  (htn : t * ↑n = 2)
  (htm : t⁻¹ * ↑m = 2)
  (hmn : n * m = 4)
  (hn : n ≠ 1)
  (hn' : n ≠ -1) :
  let α : ↥Φ := ⟨x, hx⟩,
      β : ↥Φ := ⟨t • x, ht⟩
  in t⁻¹ • (β : V) = α →
     (hr.coroot β) ↑α = ↑n →
     (hr.coroot α) ↑β = ↑m → m ≠ 1 :=
begin
  intros α β hαβ hn_1 hm,
  have := hr.two_smul_not_mem β β.property,
  contrapose! this,
  rw [this, algebra_map.coe_one, mul_one, inv_eq_iff_inv_eq] at htm,
  simpa only [nsmul_eq_smul_cast k 2, nat.cast_two, subtype.coe_mk, smul_inv_smul₀, ne.def,
                bit0_eq_zero, one_ne_zero, not_false_iff, ← htm],
end

include h
theorem m_not_neg_1 {k : Type u_1} {V : Type u_2} (n m : ℤ)
  [field k]
  [char_zero k]
  [add_comm_group V]
  [module k V]
  {Φ : set V}
  (h : is_root_system k Φ)
  (hr : is_reduced_root_system k Φ)
  (x : V)
  (hx : x ∈ Φ)
  (t : k)
  (ht : t • x ∈ Φ)
  (ht₀ : t ≠ 0)
  (htn : t * ↑n = 2)
  (htm : t⁻¹ * ↑m = 2)
  (hmn : n * m = 4)
  (hn : n ≠ 1)
  (hn' : n ≠ -1) :
  let α : ↥Φ := ⟨x, hx⟩,
      β : ↥Φ := ⟨t • x, ht⟩
  in t⁻¹ • (β : V) = α →
     (h.coroot β) ↑α = ↑n →
     (h.coroot α) ↑β = ↑m → m ≠ -1 :=
begin
  intros α β hαβ hn_1 hm,
  have := hr.two_smul_not_mem (-β) (h.neg_mem β),
  contrapose! this,
  simp only [nsmul_eq_smul_cast k 2, nat.cast_two, subtype.coe_mk, smul_neg],
  rw [this, int.cast_neg, algebra_map.coe_one, mul_neg, mul_one, neg_eq_iff_neg_eq, eq_inv_iff_eq_inv] at htm,
  rw htm,
  simpa [← neg_inv],
end

lemma is_reduced_iff (h : is_root_system k Φ) :
  is_reduced_root_system k Φ ↔ ∀ (α ∈ Φ) (t : k), t • α ∈ Φ → t = 1 ∨ t = -1 :=
begin
  refine ⟨λ hr x hx t ht, _, λ hr, ⟨h, λ α hα contra, _⟩⟩,
  { let α : Φ := ⟨x, hx⟩,
    let β : Φ := ⟨t • x, ht⟩,
    have ht₀ : t ≠ 0, { have := h.zero_not_mem, contrapose! this, rwa [this, zero_smul] at ht, },
    have hαβ : t⁻¹ • (β : V) = α,
    { rw [subtype.coe_mk, subtype.coe_mk, smul_smul, inv_mul_cancel ht₀, one_smul], },
    obtain ⟨n, hn⟩ := h.exists_int_coroot_apply_eq β α,
    have htn : t * n = 2,
    { have : βᘁ (t • α) = 2 := h.coroot_apply_self_eq_two β,
      simpa only [linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul, hn] using this },
    obtain ⟨m, hm⟩ := h.exists_int_coroot_apply_eq α β,
    have htm : t⁻¹ * m = 2,
    { have : αᘁ (t⁻¹ • β) = 2, { rw hαβ, exact h.coroot_apply_self_eq_two α, },
      simpa only [linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul, hm] using this },
    have hmn : n * m = 4,
    { have := congr_arg2 ((*) : k → k → k) htn htm,
      rw [mul_mul_mul_comm, mul_inv_cancel ht₀, one_mul] at this,
      norm_cast at this,
      exact this, },
    have hn1 : n ≠ 1,
    { have := hr.two_smul_not_mem α α.property,
      contrapose! this,
      simp only [nsmul_eq_smul_cast k 2, nat.cast_two, subtype.coe_mk],
      rw [this, algebra_map.coe_one, mul_one] at htn,
      rwa htn at ht, },
    have hnm1 : n ≠ -1,
    { have := hr.two_smul_not_mem (-α) (h.neg_mem α),
      contrapose! this,
      simp only [nsmul_eq_smul_cast k 2, nat.cast_two, subtype.coe_mk, smul_neg],
      rw [this, int.cast_neg, algebra_map.coe_one, mul_neg, mul_one, neg_eq_iff_neg_eq] at htn,
      rwa [← htn, neg_smul] at ht, },
    -- Similarly `m ≠ ± 1`. Using `hmn : n * m = 4` this means `n`, `m` both `± 2`, thus `t = ± 1`.
    have hm1 : m ≠ 1,
    { exact foo n m hr x hx t ht ht₀ htn htm hmn hn1 hnm1 hαβ hn hm, },
    have hmn1 : m ≠ -1,
    { exact m_not_neg_1 n m h hr x hx t ht ht₀ htn htm hmn hn1 hnm1 hαβ hn hm, },
    suffices : n = 2 ∨ n = -2,
    { rcases this with rfl | rfl,
      { left,
        rwa [int.cast_two, ← eq_mul_inv_iff_mul_eq₀ (ne_zero.ne (2 : k)),
          mul_inv_cancel (ne_zero.ne (2 : k))] at htn, },
      { right,
        rwa [int.cast_neg, int.cast_two, mul_neg, neg_eq_iff_neg_eq,
          ← mul_inv_eq_iff_eq_mul₀ (ne_zero.ne (2 : k)), neg_mul,
          mul_inv_cancel (ne_zero.ne (2 : k)), eq_comm] at htn, }, },
    suffices : n.nat_abs = 2,
    { cases n.nat_abs_eq with h h,
      { left, rw [h, this, nat.cast_two], },
      { right, rw [h, this, nat.cast_two], }, },
    have hn4 : n ≠ 4,
    { contrapose! hmn1,
      simpa [hmn1, mul_right_eq_self₀] using hmn, },
    have hnm4 : n ≠ -4,
    { contrapose! hmn1,
      refine eq_neg_of_eq_neg (eq_comm.mp _),
      simpa [hmn1, mul_right_eq_self₀, ← mul_neg] using hmn, },
    replace hmn := congr_arg int.nat_abs hmn,
    rw [int.nat_abs_mul, (by norm_num : (4 : ℤ).nat_abs = 4)] at hmn,
    replace hmn : n.nat_abs ∣ 4 := ⟨m.nat_abs, hmn.symm⟩,
    rcases nat.eq_one_or_two_or_four_of_div_four hmn with h | h | h,
    { exfalso,
      cases int.nat_abs_eq n,
      { rw [h, nat.cast_one] at h_1,
       exact hn1 h_1, },
      { rw [h, nat.cast_one] at h_1,
        contradiction, }, },
    { assumption, },
    { cases int.nat_abs_eq n,
      exfalso,
      { rw h at h_1,
        norm_cast at h_1, },
      { rw h at h_1,
        norm_cast at h_1, }, }, },
  { replace contra : (2 : k) • α ∈ Φ, { rwa [nsmul_eq_smul_cast k 2 α, nat.cast_two] at contra, },
    have h2 := hr α hα (2 : k) contra,
    norm_num at h2, },
end

end field

section linear_ordered_field
variables {k V : Type*} [linear_ordered_field k] [add_comm_group V] [module k V]
-- This is where theorems about bases go-
end linear_ordered_field

end is_root_system

end root_systems
