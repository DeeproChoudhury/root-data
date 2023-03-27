import root_system.basic

open set function

namespace is_root_system

structure is_base {k V ι : Type*} [linear_ordered_field k] [add_comm_group V] [module k V]
  {Φ : set V} (h : is_root_system k Φ) (b : basis ι k V) : Prop :=
(subset : range (b : ι → V) ⊆ Φ)
(is_integral : ∀ (α ∈ Φ) i, b.coord i α ∈ add_subgroup.zmultiples (1 : k))
(same_sign : ∀ (α ∈ Φ), (∀ i, 0 ≤ b.coord i α) ∨ (∀ i, b.coord i α ≤ 0))

end is_root_system
