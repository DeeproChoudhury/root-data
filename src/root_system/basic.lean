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

lemma root_ne_zero (α : Φ) : (α : V) ≠ 0 :=
λ contra, by simpa [contra] using h.coroot_apply_self_eq_two α

lemma zero_not_mem : (0 : V) ∉ Φ :=
λ contra, h.root_ne_zero ⟨0, contra⟩ rfl

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

lemma eq_coroot_of_to_pre_symmetry_image_subseteq (α : Φ) (f : module.dual k V)
  (hf₁ : f α = 2) (hf₂ : module.to_pre_symmetry (α : V) f '' Φ ⊆ Φ) :
  f = αᘁ :=
module.eq_dual_of_to_pre_symmetry_image_subseteq (h.root_ne_zero α) h.finite h.span_eq_top hf₁ hf₂
  (h.coroot_apply_self_eq_two α) (h.symmetry_of_root_image_subset α)

/-- The group of symmetries of a root system.

TODO: Define equivalences of root systems more generally and thus obtain this as the
self-equivalences of a single root system. -/
def symmetries : subgroup (V ≃ₗ[k] V) := mul_action.stabilizer (V ≃ₗ[k] V) Φ

def is_root_system_equiv {V₂ : Type*} [add_comm_group V₂] [module k V₂]
  {Φ₂ : set V₂} (h₂ : is_root_system k Φ₂) :=
{e : V ≃ₗ[k] V₂  | e '' Φ = Φ₂ }

lemma symm_equiv {α β : Type*} (f : α ≃ β) (s : set α) (d : set β) (h : f '' s = d) :
  f.symm '' d = s :=
begin
  rw ←h,
  rw equiv.symm_image_image,
end

lemma symm_root_system_equiv {V₂ : Type*} [add_comm_group V₂] [module k V₂]
  {Φ₂ : set V₂} (h₂ : is_root_system k Φ₂)
  (e : V ≃ₗ[k] V₂)
  (he : e ∈ h.is_root_system_equiv h₂) :
  e.symm ∈ h₂.is_root_system_equiv h :=
begin
  -- rw set.mem_iff at he,
  suffices : e.symm '' Φ₂ = Φ,
  { refine this, },
  exact symm_equiv e.to_equiv _ _ he,
end

/- prove symm -/
def is_root_system_equiv_symm {V₂ : Type*} [add_comm_group V₂] [module k V₂]
  {Φ₂ : set V₂} (h₂ : is_root_system k Φ₂) :
  is_root_system_equiv  h h₂ → is_root_system_equiv h₂ h :=
begin
  rintros ⟨e, he⟩,
  refine ⟨e.symm, _⟩,
  exact symm_root_system_equiv h h₂ e he,
end

@[simp] lemma mem_symmetries_iff (u : V ≃ₗ[k] V) :
  u ∈ h.symmetries ↔ u '' Φ = Φ :=
iff.rfl

lemma finite_symmetries : finite h.symmetries :=
 -- Should follow from `module.finite_stabilizer_of_finite_of_span_eq_top`
begin
 apply module.finite_stabilizer_of_finite_of_span_eq_top h.finite h.span_eq_top,
end

/-- The Weyl group of a root system. -/
-- reflections are invertible endomorphisms and sit in the endomorphism ring
-- i.e. they are all units in the automorphism group
def weyl_group : subgroup (V ≃ₗ[k] V) := subgroup.closure $ range h.symmetry_of_root

lemma weyl_group_le_symmetries : h.weyl_group ≤ h.symmetries :=
-- Should be easy via `subgroup.closure_le`
begin
  unfold weyl_group,
  rw subgroup.closure_le h.symmetries,
  rintros - ⟨α, rfl⟩,
  exact h.symmetry_of_root_image_eq α,
end

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

/-- TODO (optional) Now that we have the more general version of this used to prove
`module.is_of_fin_order_of_finite_of_span_eq_top_of_image_subseteq`, consider reimplementing this as
`module.unit.to_perm'.comp $ subgroup.inclusion h.weyl_group_le_symmetries`. -/
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

def weyl_group_to_perm'' : h.weyl_group →* equiv.perm Φ :=
module.unit.to_perm'.comp $ subgroup.inclusion h.weyl_group_le_symmetries

example {α β γ : Type*} (f : α → β) (g : β → γ) (hf: injective f) (hg : injective g) :
injective (g ∘ f) :=
begin
  refine injective.comp hg hf,
end

#check module.unit.injective_to_perm'
/-- TODO (optional) If we redefine `weyl_group_to_perm'` above then this should be easy using
`module.unit.injective_to_perm'` and `weyl_group_le_symmetries`. -/
lemma injective_weyl_group_to_perm' : injective h.weyl_group_to_perm'' :=
 injective.comp (module.unit.injective_to_perm' h.span_eq_top)
  (subgroup.inclusion_injective (weyl_group_le_symmetries h))

/-- TODO (optional) If we redefine `weyl_group_to_perm'` above then this should be easy using
`module.unit.injective_to_perm'` and `weyl_group_le_symmetries`. -/
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

example (G : Type*) [group G] (H : subgroup G) [finite G]: finite H :=
begin
  refine subgroup.finite H,
end

-- example (G : Type*) (H : Type*) [group G] [group H] (h : H ≤ G) [finite G]: finite H := sorry

/-- TODO Consider reproving this using just `weyl_group_le_symmetries` and `finite_symmetries`
above (i.e., the Weyl group is contained in the subgroup of symmetries which is finite and so it
must be finite). -/
-- We should really be using `subgroup.of_le` but this is not present in mathlib (analogous to
-- `submodule.of_le`)
lemma finite_weyl_group : finite h.weyl_group :=
begin
  suffices : finite (h.symmetries),
  {
    let f : h.weyl_group → h.symmetries := λ x, ⟨x, h.weyl_group_le_symmetries x.property⟩,
    have hf : injective f := by { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, simpa using hxy, },
    haveI := this,
    exact finite.of_injective f hf,
  },
  apply finite_symmetries,
  -- suffices : finite (equiv.perm Φ),
  -- { haveI := this,
  --   exact finite.of_injective _ h.injective_weyl_group_to_perm, },
  -- haveI : finite Φ := finite_coe_iff.mpr h.finite,
  -- exact equiv.finite_left,
end

/-- TODO (optional): use this to golf `is_root_system.coroot_symmetry_apply_eq`. -/
lemma coroot_apply_of_mem_symmetries (u : V ≃ₗ[k] V) (hu : u ∈ h.symmetries) (α : Φ) (h') :
  ⟨u α, h'⟩ᘁ = u.symm.dual_map (αᘁ) :=
begin
  have h₀ : u '' Φ = Φ := hu,
  have h₁ : u.symm '' Φ = Φ, { conv_lhs { rw [← h₀, ← image_comp], }, simp, },
  refine (h.eq_coroot_of_to_pre_symmetry_image_subseteq ⟨u α, h'⟩ _ _ _).symm,
  { simp, },
  { have : module.to_pre_symmetry (u α) (u.symm.dual_map (αᘁ)) = u * (ട α) * u.symm,
    { ext v, simp [h.symmetry_of_root_apply], },
    rw [subtype.coe_mk, this, linear_map.mul_eq_comp, linear_map.mul_eq_comp, linear_map.coe_comp,
      linear_map.coe_comp, image_comp, image_comp, linear_equiv.coe_coe, linear_equiv.coe_coe,
      linear_equiv.coe_coe, h₁, h.symmetry_of_root_image_eq α, h₀], },
end

lemma symmetry_of_root_apply_of_mem_symmetries (u : V ≃ₗ[k] V) (hu : u ∈ h.symmetries) (α : Φ) (h') :
  ട ⟨u α, h'⟩ = u * (ട α) * u.symm :=
begin
  ext v,
  erw linear_map.mul_apply,
  rw [h.symmetry_of_root_apply, coroot_apply_of_mem_symmetries],
  simp only [subtype.coe_mk, linear_equiv.coe_to_linear_map],
  rw h.symmetry_of_root_apply,
  simp only [linear_equiv.map_sub, linear_equiv.apply_symm_apply, linear_equiv.map_smulₛₗ,
  ring_hom.id_apply, sub_right_inj],
  congr,
  exact hu,
end

end is_root_system
