import roots
import analysis.quaternion
import analysis.inner_product_space.dual
import analysis.normed_space.pointwise

noncomputable theory

variables {V : Type*} [add_comm_group V] [module ℝ V]

open_locale quaternion real_inner_product_space pointwise

local notation `e₁` := quaternion_algebra.mk 1 0 0 0 -- `1`
local notation `e₂` := quaternion_algebra.mk 0 1 0 0 -- `i`
local notation `e₃` := quaternion_algebra.mk 0 0 1 0 -- `j`
local notation `e₄` := quaternion_algebra.mk 0 0 0 1 -- `k`

def s : ℍ[ℝ] := quaternion_algebra.mk (1/2) (1/2) (1/2) (1/2)

/-- Lipshitz quaternion. -/
def quat_int : add_subgroup ℍ[ℝ] := add_subgroup.closure {e₁, e₂, e₃, e₄}

/-- Hurwitz quaternion. -/
def f4_lattice : add_subgroup ℍ[ℝ] := add_subgroup.closure {s, e₂, e₃, e₄}

lemma mem_f4_lattice_iff (q : ℍ[ℝ]) :
  q ∈ f4_lattice ↔ q ∈ quat_int ∨ q + s ∈ quat_int :=
begin
  split,
  intro h,
  left,
  assume q hq,
  -- { intro h,
  --   have : q ∈ add_subgroup.closure {s, e₂, e₃, e₄} := h,
  --   rw add_subgroup.mem_closure_iff at this,
  --   rcases this with ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩,
  --   suffices : a • s + b • e₂ + c • e₃ + d • e₄ ∈ quat_int,
  --   { simpa, },
  --   rw add_subgroup.mem_closure_iff,
  --   refine ⟨a, b, c, d, ha, hb, hc, hd, _⟩,
  -- }
end

/- Remarkable fact: this lattice is actually a subring. May or may not be useful.

def f4_order : subring ℍ[ℝ] :=
{ one_mem' := sorry,
  mul_mem' := sorry,
  .. f4_lattice }
-/

def f4_root_system : set (ℍ[ℝ]) := {q : ℍ[ℝ] | ‖q‖^2 ≤ 2 ∧ q ∈ f4_lattice}

lemma is_root_system_f4_root_system : is_root_system ℝ f4_root_system :=
{ finite :=
  begin
    sorry,
  end,
  span_eq_top :=
  begin
    sorry,
  end,
  exists_dual :=
  begin
    intros α hα,
    have : ‖α‖ * ‖α‖ ≠ 0, { sorry, },
    let α' := (2 / (‖α‖*‖α‖)) • α,
    refine ⟨(inner_product_space.to_dual_map ℝ ℍ[ℝ] α').to_linear_map, _, _⟩,
    { simp only [continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe,
        inner_product_space.to_dual_map_apply, inner_smul_left, is_R_or_C.conj_to_real,
        quaternion.inner_self, quaternion.norm_sq_eq_norm_sq, div_mul_cancel _ this], },
    { rintros - ⟨β, hβ, rfl⟩,
      suffices : β - (2 / (‖α‖ * ‖α‖) * inner α β) • α ∈ f4_root_system, { simpa, },
      -- There are only finitely-many (in fact 48) possible `α` and `β`. We could therefore
      -- use a mathematically low-tech but computer-sciencey high-tech proof that brute forces
      -- all cases to generate a proof, using some Lean meta code.
      sorry, },
  end,
  subset_zmultiples :=
  begin
    rintros α hα f ⟨hf, hf'⟩ - ⟨β, hβ, rfl⟩,
    -- Likewise actually a finite calculation.
    sorry,
  end, }
