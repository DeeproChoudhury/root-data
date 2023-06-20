import root_system.basic

open set function

namespace is_root_system

structure is_base {k V ι : Type*} [linear_ordered_field k] [add_comm_group V] [module k V]
  {Φ : set V} (h : is_root_system k Φ) (b : basis ι k V) : Prop :=
(subset : range (b : ι → V) ⊆ Φ)
(is_integral : ∀ (α ∈ Φ) i, b.coord i α ∈ add_subgroup.zmultiples (1 : k))
(same_sign : ∀ (α ∈ Φ), (∀ i, 0 ≤ b.coord i α) ∨ (∀ i, b.coord i α ≤ 0))

variables {k : Type*} {V : Type*} [linear_ordered_field k] [add_comm_group V] [module k V]
/-- Regular -/
structure is_regular (Φ : set V) (f : module.dual k V) : Prop :=
(regularity : ∀ α ∈ Φ, f α ≠ 0)

/-- Positive and Negative roots -/
def positive_roots (Φ : set V) (v : module.dual k V) (h : is_regular Φ v) : set V :=
{α ∈ Φ | 0 < v α}

def negative_roots (Φ : set V) (v : module.dual k V) (h : is_regular Φ v) : set V :=
{α ∈ Φ | v α < 0}

/-- Decomposable and Indecomposable roots -/
def is_decomposable (Φ : set V) (v : module.dual k V) (h :is_regular Φ v) (α : V) : Prop :=
α ∈ positive_roots Φ v h ∧ ∃ (β γ : V), β ∈ positive_roots Φ v h ∧ γ ∈ positive_roots Φ v h ∧ α = β + γ

def is_indecomposable (Φ : set V) (v : module.dual k V) (h : is_regular Φ v) (α : V) : Prop :=
α ∈ positive_roots Φ v h ∧ ∀ (β γ : V), β ∈ positive_roots Φ v h ∧ γ ∈ positive_roots Φ v h → α ≠ β + γ

-- lemma indecomposable_diff_not_root (Φ : set V) (v : module.dual k V) (h : is_regular Φ v) (α β : V) :
--   is_indecomposable Φ v h α ∧ is_indecomposable Φ v h β → α - β ∉ Φ :=
-- begin
--   sorry,
-- end

end is_root_system
