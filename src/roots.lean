import linear_algebra.dual
import linear_algebra.contraction
import linear_algebra.bilinear_form
import data.sign

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

-- example: char_zero k := strict_ordered_semiring.to_char_zero

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

end module

section root_systems

/-- A crystallographic root system (possibly non-reduced). -/
@[protect_proj]
class is_root_system (k : Type*) {V : Type*} [comm_ring k] [char_zero k] [add_comm_group V] [module k V]
(Φ : set V) : Prop :=
(finite : set.finite Φ)
(span_eq_top : submodule.span k Φ = ⊤)
(exists_dual : ∀ α ∈ Φ, ∃ f : module.dual k V, f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ)
(subset_zmultiples : ∀ (α ∈ Φ) (f : module.dual k V),
  f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ → f '' Φ ⊆ add_subgroup.zmultiples (1 : k))
/-image of phi under the map f is a subset copy of the integers that live in k -/


instance is_root_system_set_finite (k : Type*) (V : Type*) {Φ : set V}
[comm_ring k] [char_zero k] [add_comm_group V] [module k V] [is_root_system k Φ] : fintype Φ
:=
-- by infer_instance
begin
  refine finite.fintype _,
  exact is_root_system.finite k,
  -- letI := classical.dec_eq V,
end

/-- A reduced, crystallographic root system. -/
structure is_reduced_root_system (k : Type*) {V : Type*} [comm_ring k] [char_zero k] [add_comm_group V] [module k V]
(Φ : set V) extends is_root_system k Φ : Prop :=
(two_smul_not_mem : ∀ α ∈ Φ, 2 • α ∉ Φ)

namespace is_root_system

/-- Need ordering for base, k and V are locally shadowing here-/
structure is_base {k V ι : Type*} [linear_ordered_field k] [add_comm_group V] [module k V]
{Φ : set V} (h : is_root_system k Φ)
(b : basis ι k V) : Prop :=
(is_integral: ∀ (α ∈ Φ) i, b.coord i α ∈ add_subgroup.zmultiples (1 : k))
(same_sign: ∀ (α ∈ Φ), (∀ i, 0 ≤ b.coord i α) ∨ (∀ i, b.coord i α ≤ 0))

section field

variables {k V : Type*} [field k] [char_zero k] [add_comm_group V] [module k V]

variables {Φ : set V} (h : is_root_system k Φ)
include h

-- #check @basis.mk _ k V _ _ _ _
-- def has_base (b : set V) : Prop := b ⊆ Φ ∧ linear_independent k (coe : b → V) ∧ submodule.span k b = ⊤
-- ∧ more conditions

-- def has_base {ι : Type*} (b : basis ι k V) : Prop := ∀ (α ∈ Φ) (i : ι),
-- b.coord i α ∈ add_subgroup.zmultiples (1 : k)
-- ∧ ((∀ (i : ι),  ) ∨ (∀ (i : ι), sign_neg))



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
units.ext $ module.to_pre_symmetry_sq $ coroot_apply_self_eq_two h α
-- module.to_pre_symmetry_sq $ _--module.to_pre_symmetry_sq $ h.coroot_apply_self_eq_two α
#print axioms symmetry_of_root_sq
#check @funext
#print axioms funext
#print axioms classical.choice

@[simp] lemma symmetry_of_root_image_subset (α : Φ) :
  h.symmetry_of_root α '' Φ ⊆ Φ :=
(classical.some_spec (h.exists_dual _ α.property)).2

example (X : Type*) (x : X) (S : set X) (hs : S ⊆ {x}) (hs': S.nonempty) : S = {x} :=
begin
  ext y,
  rw [mem_singleton_iff],
  simp only [subset_singleton_iff] at hs,
  refine ⟨λ hy, hs _ hy, _⟩,
  rintros rfl,
  obtain ⟨p, hp⟩ := hs',
  rwa ←hs _ hp,
end


@[simp] lemma neg_mem (α : Φ) : - (α : V) ∈ Φ :=
begin
  have := (image_subset_iff.mp $ h.symmetry_of_root_image_subset α) α.property,
  simpa only [subtype.val_eq_coe, mem_preimage, symmetry_of_root_apply_self_neg] using this,
end

@[simp] lemma coroot_image_subset_zmultiples (α : Φ) :
  h.coroot α '' Φ ⊆ add_subgroup.zmultiples (1 : k) :=
h.subset_zmultiples α α.property (h.coroot α)
  ⟨h.coroot_apply_self_eq_two α, h.symmetry_of_root_image_subset α⟩

@[simp] lemma coroot_apply_mem_zmultiples (α β : Φ) :
  h.coroot α β ∈ add_subgroup.zmultiples (1 : k) :=
begin
  have := (image_subset_iff.mp $ h.coroot_image_subset_zmultiples α) β.property,
  simpa using this,
end

@[simp] lemma coroot_apply_mem_zmultiples_2 (α β : Φ) :
  ∃ a : ℤ, h.coroot α β = a :=
begin
  have hr := h.coroot_apply_mem_zmultiples α β,
  rw add_subgroup.mem_zmultiples_iff at hr,
  simp only [int.smul_one_eq_coe] at hr,
  obtain ⟨a, ha⟩ := hr,
  use a,
  rw ha,
  -- simp_rw [eq_comm],
  -- assumption,
end

lemma exists_int_coroot_apply_eq (α β : Φ) :
  ∃ (n : ℤ), h.coroot α β = n :=
begin
  obtain ⟨n, hn⟩ := add_subgroup.mem_zmultiples_iff.mp (h.coroot_apply_mem_zmultiples α β),
  rw ← hn,
  exact ⟨n, by simp⟩,
end

lemma zero_not_mem : (0 : V) ∉ Φ :=
λ contra, by simpa using h.coroot_apply_self_eq_two ⟨0, contra⟩

/-- The Weyl group of a root system. -/
-- reflections are invertible endomorphisms and sit in the endomorphism ring
-- i.e. they are all units in the automorphism group
def weyl_group : subgroup $ (module.End k V)ˣ := subgroup.closure $ range h.symmetry_of_root
#check has_vadd.vadd
-- w acts on α and sends roots to roots (acts on roots)
-- w acting on α gives a root, not a random vector
lemma weyl_group_apply_root_mem (w : h.weyl_group) (α : Φ) : w • (α : V) ∈ Φ :=
begin
  obtain ⟨w, hw⟩ := w,
  change w • (α : V) ∈ Φ,
  -- induction w generalizing α,
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

-- TODO (maybe) Upgrade to `h.weyl_group →* equiv.perm Φ`
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
#check h.weyl_group_to_perm

-- Use `h.span_eq_top`.
lemma injective_weyl_group_to_perm : injective h.weyl_group_to_perm' :=
begin
  rw ←monoid_hom.ker_eq_bot_iff, -- Injective is the same as ker = ⊥
  rw eq_bot_iff,
  intros w hw, -- Let w ∈ ker f
  rw subgroup.mem_bot, -- w ∈ ⊥ ↔ w = 1
  rw monoid_hom.mem_ker at hw, -- x ∈ ker f ↔ f x = 1
  have hw' := fun_like.congr_fun hw, --Functions are equal if that agree for all values
  change ∀ x, _ = x at hw',
  -- intros x y hw,
  ext v,
  change w v = v,
  -- have := h.span_eq_top,
  have := fun_like.congr_fun hw,
  sorry,
end

-- Use `injective_weyl_group_to_perm`.
lemma finite_weyl_group : finite h.weyl_group := sorry

/- Roots span the space and roots are finite so each root symmetry just permutes the roots. Therefore
the Wyel group is a subgroup of the symmetry group
subgroups closure induction-/

/-- The linear map `V → V⋆` induced by a root system. -/
def to_dual : V →ₗ[k] module.dual k V :=
{ to_fun := λ x, ∑ᶠ α, (h.coroot α x) • h.coroot α,
  map_add' :=
  begin
    intros x y,
    ext,
    simp only [linear_map.map_add, map_add],
    simp only [linear_map.add_apply],
    simp_rw [add_smul],
    rw finsum_add_distrib,
    simp only [linear_map.add_apply],

--    push_cast,

    -- change ∑ᶠ α, (h.coroot α x + h.coroot α y) • h.coroot α = ∑ᶠ α, (h.coroot α x) • h.coroot α + ∑ᶠ α, (h.coroot α y) • h.coroot α,
    sorry,
    sorry,
  end,
  map_smul' := λ c x, by { ext, simp only [linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul, linear_map.smul_apply],
   sorry, }, }

example (a b : k) (c : module.dual k V) : (a * b) • c = a • (b • c) := (smul_smul a b c).symm

  /-- The linear map `V → V⋆` induced by a root system. -/
def to_dual_2 : V →ₗ[k] module.dual k V :=
{ to_fun := λ x, ∑ (α : Φ), (h.coroot α x) • h.coroot α,
  map_add' :=
  begin
    intros x y,
    ext,
    simp only [linear_map.map_add, map_add, linear_map.add_apply],
    simp_rw [add_smul],
    rw finset.sum_add_distrib,
    rw linear_map.add_apply,
  end,
  map_smul' :=
  begin
    intros c x,
    ext,
    simp only [linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul, linear_map.smul_apply],
    simp_rw [← smul_smul],
    rw [← finset.smul_sum],
    rw linear_map.smul_apply,
    rw smul_eq_mul,

    -- simp,
    -- sorry,
  end
}

/-- to_dual is really a bilinear form which gives you a number. This is the Euclidean form-/
lemma to_dual_apply_apply (x y : V) :
h.to_dual_2 x y = ∑ (α : Φ), (h.coroot α x) • h.coroot α y :=
begin
 have := h.to_dual_2.map_add' x y,
-- rw ←linear_map.to_fun_eq_coe,
 change (∑ (α : Φ), (h.coroot α x) • h.coroot α) y = _,
 simp only [linear_map.coe_fn_sum, fintype.sum_apply, linear_map.smul_apply],
--  rw finset.sum_apply,
--  rw [← to_dual_2.to_fun],
end

lemma to_dual_apply_apply_2 (x y : V) :
h.to_dual x y = ∑ᶠ α, (h.coroot α x) • h.coroot α y :=
begin
 have := h.to_dual.map_add x y,
 specialize this,
 sorry,
end

/-- The bilinear map on `V` induced by a root system. -/
def to_bilinear_map : V →ₗ[k] V →ₗ[k] k :=
{ to_fun := λ x, h.to_dual x,
  map_add' := λ x y, by { ext, simp only [map_add], },
  map_smul' := λ c x, by { ext, simp only [linear_map.map_smulₛₗ], }
}

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




example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
⟨hP, hQ⟩


example : set ℕ := {x : ℕ | x ^ 2 = 4 }
example : Type := {x : ℕ // x ^ 2 = 4}

-- example : (0 : k) ≠ (1 : k) := by norm_num
-- example (x : k) : x ≠ x + 1 := begin
--   hint,
--   sorry
-- end

-- --Statement, allowed
-- def nottrueatall : Prop := 2 + 2 = 5
-- -- Proof that 2 + 2 = 5, not allowed
-- def foo  :nottrueatall :=
-- begin
--   unfold nottrueatall,
-- end

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

lemma div {n : ℕ} (h : n ∣ 4) : n = 1 ∨ n = 2 ∨ n = 4 :=
begin
  have h₁ := nat.le_of_dvd four_pos h,
  interval_cases n with h;
  revert h;
  dec_trivial,
end

lemma deduce_m {m : ℤ} (h : 4 * m = 4) : m = 1 :=
begin
  conv_rhs at h { rw ← mul_one (4 : ℤ), },
  have h_pos : 0 < (4 : ℤ) := by positivity,
  exact mul_left_cancel₀ h_pos.ne' h,
end

lemma deduce_m_neg {m : ℤ} (h : (-4) * m = 4) : m = -1 :=
begin
  conv_rhs at h { rw [ ← mul_one (4 : ℤ), ← neg_mul_neg], },
  have h_pos : (-4 : ℤ) < 0 := by norm_num,
  exact mul_left_cancel₀ h_pos.ne h,
end

lemma is_reduced_iff (h : is_root_system k Φ) :
  is_reduced_root_system k Φ ↔ ∀ (α ∈ Φ) (t : k), t • α ∈ Φ → t = 1 ∨ t = -1 :=
begin
  split,
--  refine ⟨λ hr x hx t ht, _, λ hr, ⟨h, λ α hα contra, _⟩⟩,
  { intros hr x hx t ht,
    let α : Φ := ⟨x, hx⟩,
    let β : Φ := ⟨t • x, ht⟩,
    have ht₀ : t ≠ 0, { have := h.zero_not_mem, contrapose! this, rwa [this, zero_smul] at ht, },
    have hαβ : t⁻¹ • (β : V) = α,
    { rw [subtype.coe_mk, subtype.coe_mk, smul_smul, inv_mul_cancel ht₀, one_smul], },
    obtain ⟨n, hn⟩ := h.exists_int_coroot_apply_eq β α,
    have htn : t * n = 2,
    { have : h.coroot β (t • α) = 2 := h.coroot_apply_self_eq_two β,
      simpa only [linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul, hn] using this },
    obtain ⟨m, hm⟩ := h.exists_int_coroot_apply_eq α β,
    have htm : t⁻¹ * m = 2,
    { have : h.coroot α (t⁻¹ • β) = 2, { rw hαβ, exact h.coroot_apply_self_eq_two α, },
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
    { exact foo n m hr x hx t ht ht₀ htn htm hmn hn1 hnm1 hαβ hn hm,
    },
    have hmn1 : m ≠ -1,
    {
      exact m_not_neg_1 n m h hr x hx t ht ht₀ htn htm hmn hn1 hnm1 hαβ hn hm,
      -- have := hr.two_smul_not_mem (-β) (h.neg_mem β),
      -- contrapose! this,
      -- simp only [nsmul_eq_smul_cast k 2, nat.cast_two, subtype.coe_mk, smul_neg],
      -- rw [this, int.cast_neg, algebra_map.coe_one, mul_neg, mul_one, neg_eq_iff_neg_eq, eq_inv_iff_eq_inv] at htm,
      -- rw htm,
      -- simpa [← neg_inv],
    },
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
    {
      by_contra,
      rw h at hmn,
      replace hmn := deduce_m hmn,
      contradiction,
    },
    have hnm4 : n ≠ -4,
    {
      by_contra,
      rw h at hmn,
      replace hmn := deduce_m_neg hmn,
      contradiction,
    },
    replace hmn := congr_arg int.nat_abs hmn,
    rw [int.nat_abs_mul, (by norm_num : (4 : ℤ).nat_abs = 4)] at hmn,
    replace hmn : n.nat_abs ∣ 4 := ⟨m.nat_abs, hmn.symm⟩,
    rcases div hmn with h | h | h,
    {
      exfalso,
      cases int.nat_abs_eq n,
      {rw [h, nat.cast_one] at h_1,
      --  rw nat.cast_one at h_1,
       exact hn1 h_1, },
      { rw [h, nat.cast_one] at h_1,
        -- rw nat.cast_one at h_1,
        contradiction, },
    },
    {
      assumption, },
    {
      cases int.nat_abs_eq n,
      exfalso,
      {
       rw h at h_1,
       norm_cast at h_1, },
      {
       rw h at h_1,
       norm_cast at h_1, },
     },
      },
  { -- λ hr, ⟨h, λ α hα contra, _⟩
    intro hr,
    refine ⟨h, _⟩,
    intros α hα contra,
    replace contra : (2 : k) • α ∈ Φ, { rwa [nsmul_eq_smul_cast k 2 α, nat.cast_two] at contra, },
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
