import roots

open_locale tensor_product big_operators
open set function

example {k : Type*} [linear_ordered_field k] : char_zero k := strict_ordered_semiring.to_char_zero

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


@[protect_proj]
class is_root_system' (k : Type*) {V : Type*} [comm_ring k] [char_zero k] [add_comm_group V] [module k V]
(Φ : set V) [fintype Φ] : Prop :=
(span_eq_top : submodule.span k Φ = ⊤)
(exists_dual : ∀ α ∈ Φ, ∃ f : module.dual k V, f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ)
(subset_zmultiples : ∀ (α ∈ Φ) (f : module.dual k V),
  f α = 2 ∧ module.to_pre_symmetry α f '' Φ ⊆ Φ → f '' Φ ⊆ add_subgroup.zmultiples (1 : k))

#print axioms is_root_system.symmetry_of_root_sq
#check @funext
#print axioms funext
#print axioms classical.choice

#check has_vadd.vadd

example {k V : Type*} [field k] [add_comm_group V] [module k V] (a b : k) (c : module.dual k V) :
  (a * b) • c = a • (b • c) :=
(smul_smul a b c).symm



  /-- The linear map `V → V⋆` induced by a root system. -/
-- def to_dual_2 : V →ₗ[k] module.dual k V :=
-- { to_fun := λ x, ∑ (α : Φ), (h.coroot α x) • h.coroot α,
--   map_add' :=
--   begin
--     intros x y,
--     ext,
--     simp only [linear_map.map_add, map_add, linear_map.add_apply],
--     simp_rw [add_smul],
--     rw finset.sum_add_distrib,
--     -- simp,
--     rw linear_map.add_apply,
--   end,
--   map_smul' :=
--   begin
--     intros c x,
--     ext,
--     simp only [linear_map.map_smulₛₗ, ring_hom.id_apply, algebra.id.smul_eq_mul, linear_map.smul_apply],
--     simp_rw [← smul_smul],
--     rw [← finset.smul_sum],
--     rw linear_map.smul_apply,
--     rw smul_eq_mul,

--     -- simp,
--     -- sorry,
--   end
-- }

-- to_dual is really a bilinear form which gives you a number. This is the Euclidean form-/
-- lemma to_dual_apply_apply (x y : V) :
-- h.to_dual_2 x y = ∑ (α : Φ), (h.coroot α x) • h.coroot α y :=
-- begin
--  have := h.to_dual_2.map_add' x y,
-- -- rw ←linear_map.to_fun_eq_coe,
--  change (∑ (α : Φ), (h.coroot α x) • h.coroot α) y = _,
--  simp only [linear_map.coe_fn_sum, fintype.sum_apply, linear_map.smul_apply],
-- --  rw finset.sum_apply,
-- --  rw [← to_dual_2.to_fun],
-- end

-- lemma finsum_apply {α : Type*} {M : Type*} [add_comm_monoid M] (f : α → M) (a : α) (hf : (support f).finite)
-- : (∑ᶠ c : α, f c) a = (∑ c in hf.to_finite, f c a) :=

-- lemma finsum_apply' {α : Type*} {β : α → Type*} {γ} [∀a, comm_monoid (β a)]
-- (a : α) (g : γ → Πa, β a) (hg : (support f).finite) :

-- lemma finsum_apply_2 {α : Type*} {β : α → Type*} {γ : Type*} {M : Type*} [Π (a : α), add_comm_monoid (β a)]
-- [add_comm_monoid M] (a : α) (s : γ) (f : α → M) (hf : (support f).finite) (g : γ → Π (a : α), β a) :
-- (∑ᶠ c : α, f c) a = (∑ c in hf.to_finset, f c a) :=

example {β : Type*} {s : set β} [finite β]
  (M : Type*) [add_comm_monoid M] [f : s → M] (p : s):
(∑ᶠ (α : s), f) p = ∑ᶠ (α : s), f p
:=
begin
  have h1 : (support (λ (i : ↥s), f)).finite,
  {
    apply set.to_finite,
  },
  rw [finsum_eq_sum (λ (i : ↥s), f) h1],
  have h2 : (support (λ (i : ↥s), f p)).finite,
  {
    apply set.to_finite,
  },
  rw [finsum_eq_sum (λ (i : ↥s), f p) h2],
  simp only [finset.sum_apply],
  congr';
  sorry,
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
