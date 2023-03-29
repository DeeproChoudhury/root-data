import root_system.basic

open set function

/-- A reduced, crystallographic root system. -/
structure is_reduced_root_system (k : Type*) {V : Type*}
  [comm_ring k] [char_zero k] [add_comm_group V] [module k V] (Φ : set V)
  extends is_root_system k Φ : Prop :=
(two_smul_not_mem : ∀ α ∈ Φ, 2 • α ∉ Φ)

namespace is_root_system

variables {k V : Type*} [field k] [char_zero k] [add_comm_group V] [module k V]
variables {Φ : set V} (h : is_root_system k Φ)

local postfix `ᘁ`:100 := h.coroot
local notation `ട` := h.symmetry_of_root

theorem foo {k : Type*} {V : Type*} (n m : ℤ)
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

theorem m_not_neg_1 {k : Type*} {V : Type*} (n m : ℤ)
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

end is_root_system
