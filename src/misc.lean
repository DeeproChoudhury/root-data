import data.set.finite
import tactic.interval_cases

open function

-- This may already exist in some form in Mathlib.
lemma equiv.symm_apply_mem_of_forall_mem_finite {α : Type*} (e : α ≃ α) {s : set α}
  (h_mem : ∀ x : s, e x ∈ s) (h_fin : s.finite) (x : s) :
  e.symm (x : α) ∈ s :=
begin
  haveI : fintype s := set.finite.fintype h_fin,
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
