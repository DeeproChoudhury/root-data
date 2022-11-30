import linear_algebra.dual
import linear_algebra.contraction
import linear_algebra.bilinear_form

noncomputable theory

open_locale tensor_product big_operators
open set function

variables {k V : Type*} [field k] [char_zero k] [add_comm_group V] [module k V]

namespace module

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

end module

section root_systems

variables (k)

/-- A crystallographic root system (possibly non-reduced). -/
@[protect_proj]
structure is_root_system (Φ : set V) : Prop :=
(finite : finite Φ)
(span_eq_top : submodule.span k Φ = ⊤)
(exists_dual : ∀ α ∈ Φ, ∃ f : module.dual k V, f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ)
(subset_zmultiples : ∀ α (f : module.dual k V),
  f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ → f '' Φ ⊆ add_subgroup.zmultiples (1 : k))

/-- A reduced, crystallographic root system. -/
structure is_reduced_root_system (Φ : set V) extends is_root_system k Φ : Prop :=
(two_smul_not_mem : ∀ α ∈ Φ, 2 • α ∉ Φ)

variables {k}

namespace is_root_system

variables {Φ : set V} (h : is_root_system k Φ)
include h

/-- The coroot of a root.

Note that although this uses `classical.some`, the choice is unique (TODO Formalise this). -/
def coroot (α : Φ) : module.dual k V := classical.some $ h.exists_dual _ α.property

@[simp] lemma coroot_apply_self_eq_two (α : Φ) :
  h.coroot α α = 2 :=
(classical.some_spec (h.exists_dual _ α.property)).1

/-- The symmetry associated to a root. -/
def symmetry_of_root (α : Φ) : units (module.End k V) :=
module.to_symmetry $ h.coroot_apply_self_eq_two α

@[simp] lemma symmetry_of_root_apply_self_neg (α : Φ) :
  h.symmetry_of_root α α = - α :=
module.to_pre_symmetry_apply_self $ h.coroot_apply_self_eq_two α

lemma symmetry_of_root_sq (α : Φ) : (h.symmetry_of_root α)^2 = 1 :=
sorry

lemma zero_not_mem : (0 : V) ∉ Φ :=
λ contra, by simpa using h.coroot_apply_self_eq_two ⟨0, contra⟩

/-- The Weyl group of a root system. -/
def weyl_group : subgroup $ units (module.End k V) := subgroup.closure $ range h.symmetry_of_root

-- Estimate high effort.
lemma finite_weyl_group : finite h.weyl_group := sorry

/-- The linear map `V → V⋆` induced by a root system. -/
def to_dual : V →ₗ[k] module.dual k V :=
{ to_fun := λ x, ∑ᶠ α, (h.coroot α x) • h.coroot α,
  map_add' := sorry,
  map_smul' := sorry, }

/-- The bilinear map on `V` induced by a root system. -/
def to_bilinear_map : V →ₗ[k] V →ₗ[k] k :=
{ to_fun := λ x, h.to_dual x,
  map_add' := sorry,
  map_smul' := sorry, }

/-- The bilinear form on `V` induced by a root system. -/
def to_bilin_form : bilin_form k V := h.to_bilinear_map.to_bilin

-- Estimate medium effort.
@[simp] lemma to_bilin_form_weyl_eq (g : h.weyl_group) (x y : V) :
  h.to_bilin_form (g • x) (g • y) = h.to_bilin_form x y :=
begin
  sorry,
end

-- Estimate high effort.
lemma to_bilin_form_orthogonal_eq_ker (α : Φ) :
  h.to_bilin_form.orthogonal (k ∙ (α : V)) = (h.coroot α).ker :=
begin
  sorry,
end

-- Estimate low effort.
lemma is_reduced_iff (h : is_root_system k Φ) :
  is_reduced_root_system k Φ ↔ ∀ (α ∈ Φ) (t : k), t • α ∈ Φ → t = 1 ∨ t = -1 :=
begin
  sorry,
end

end is_root_system

end root_systems
