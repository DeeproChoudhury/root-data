import linear_algebra_aux
import misc

noncomputable theory

open_locale pointwise
open set function

/-- A crystallographic root system (possibly non-reduced). -/
@[protect_proj]
class is_root_system (k : Type*) {V : Type*}
  [comm_ring k] [char_zero k] [add_comm_group V] [module k V] (Φ : set V) : Prop :=
(finite : Φ.finite)
(span_eq_top : submodule.span k Φ = ⊤)
(exists_dual : ∀ α ∈ Φ, ∃ f : module.dual k V, f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ)
(subset_zmultiples : ∀ (α ∈ Φ) (f : module.dual k V),
  f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ → f '' Φ ⊆ add_subgroup.zmultiples (1 : k))

namespace is_root_system

variables {k V : Type*} [field k] [char_zero k] [add_comm_group V] [module k V]
variables {Φ : set V} (h : is_root_system k Φ)
include h

/-- The coroot of a root.

Note that although this uses `classical.some`, the choice is unique (see Serre's lemma). -/
def coroot (α : Φ) : module.dual k V := classical.some $ h.exists_dual _ α.property

local postfix `ᘁ`:100 := h.coroot

@[simp] lemma coroot_apply_self_eq_two (α : Φ) :
  αᘁ α = 2 :=
(classical.some_spec (h.exists_dual _ α.property)).1

@[simp] lemma coroot_to_pre_symmetry_subset (α : Φ) :
  module.to_pre_symmetry (α : V) (αᘁ) '' Φ ⊆ Φ :=
(classical.some_spec (h.exists_dual _ α.property)).2

lemma zero_not_mem : (0 : V) ∉ Φ :=
λ contra, by simpa using h.coroot_apply_self_eq_two ⟨0, contra⟩

/-- The symmetry associated to a root. -/
def symmetry_of_root (α : Φ) : V ≃ₗ[k] V :=
module.to_symmetry $ h.coroot_apply_self_eq_two α

local notation `ട` := h.symmetry_of_root

lemma symmetry_of_root_apply (α : Φ) (v : V) :
  ട α v = v - αᘁ v • α :=
module.to_pre_symmetry_apply (α : V) v (αᘁ)

@[simp] lemma symmetry_of_root_apply_self_neg (α : Φ) :
  ട α α = - α :=
module.to_pre_symmetry_apply_self $ h.coroot_apply_self_eq_two α

@[simp] lemma symmetry_of_root_sq (α : Φ) : (ട α)^2 = 1 :=
begin
  ext v,
  have := (module.to_pre_symmetry_sq (coroot_apply_self_eq_two h α)),
  exact linear_map.congr_fun this v,
end

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
def weyl_group : subgroup (V ≃ₗ[k] V) := subgroup.closure $ range h.symmetry_of_root

@[simp] lemma symmetry_mem_weyl_group (α : Φ) :
  ട α ∈ h.weyl_group :=
subgroup.subset_closure $ mem_range_self α

-- w acts on α and sends roots to roots (acts on roots)
-- w acting on α gives a root, not a random vector
lemma weyl_group_apply_root_mem (w : h.weyl_group) (α : Φ) : w • (α : V) ∈ Φ :=
begin
  obtain ⟨w, hw⟩ := w,
  change w • (α : V) ∈ Φ,
  revert α,
  have : ∀ (g : V ≃ₗ[k] V), g ∈ range h.symmetry_of_root → ∀ (α : Φ), g • (α : V) ∈ Φ,
  { rintros - ⟨β, rfl⟩ α, exact h.symmetry_of_root_image_subset β ⟨α, α.property, rfl⟩, },
  -- Look up what this means
  refine subgroup.closure_induction hw this _ (λ g₁ g₂ hg₁ hg₂ α, _) (λ g hg α, _),
  { simp, },
  { rw mul_smul, exact hg₁ ⟨_, hg₂ α⟩, },
  { let e : V ≃ V := ⟨λ x, g • x, λ x, g.symm • x, λ x, by simp, λ x, by simp⟩,
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
  { exact linear_equiv.map_zero _, },
  { intros x y hx hy,
    erw linear_equiv.map_add,
    change w x + w y = x + y,
    rw [hx, hy], },
  { intros t x hx,
    erw linear_equiv.map_smul,
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

end is_root_system
