import linear_algebra.dual

noncomputable theory

open set function

namespace module

variables (R M : Type*) [comm_ring R] [add_comm_group M] [module R M]

@[simp] lemma flip_dual_eval : (dual.eval R M).flip = linear_map.id :=
begin
  ext,
  simp only [linear_map.flip_apply, linear_equiv.coe_coe, linear_equiv.of_bijective_apply,
    dual.eval_apply, linear_map.id_coe, id.def],
end

@[simp] lemma _root_.linear_map.dual_map_comp_dual_eval
  (N : Type*) [add_comm_monoid N] [module R N] (e : M →ₗ[R] dual R N) :
  (e.dual_map : dual R (dual R N) →ₗ[R] dual R M) ∘ₗ dual.eval R N = e.flip :=
rfl

section is_reflexive

/-- A reflexive `R`-module `M` is one for which the natural map: `M → dual R (dual R M)` is a
bijection. -/
class is_reflexive : Prop :=
(bijective_dual_eval [] : bijective $ dual.eval R M)

def eval_equiv' [is_reflexive R M] : M ≃ₗ[R] dual R (dual R M) :=
linear_equiv.of_bijective _ $ is_reflexive.bijective_dual_eval R M

@[simp] lemma apply_eval_equiv'_symm_apply [is_reflexive R M]
  (f : module.dual R M) (g : module.dual R $ module.dual R M) :
  f ((eval_equiv' R M).symm g) = g f :=
begin
  set n := (eval_equiv' R M).symm g,
  have hn : g = eval_equiv' R M n := (linear_equiv.apply_symm_apply _ _).symm,
  rw hn,
  refl,
end

lemma symm_dual_map_eval_equiv' [is_reflexive R M] :
  ↑(eval_equiv' R M).dual_map.symm = dual.eval R (dual R M) :=
begin
  ext f g,
  simp only [linear_equiv.dual_map_symm, linear_equiv.coe_coe, linear_equiv.dual_map_apply,
    apply_eval_equiv'_symm_apply, dual.eval_apply],
end

instance [is_reflexive R M] : is_reflexive R (dual R M) :=
⟨by { rw ← symm_dual_map_eval_equiv', exact (eval_equiv' R M).dual_map.symm.bijective, }⟩

instance is_reflexive_of_finite_free [module.finite R M] [module.free R M] [nontrivial R] :
  is_reflexive R M :=
⟨⟨linear_map.ker_eq_bot.mp (free.choose_basis R M).eval_ker,
  linear_map.range_eq_top.mp (free.choose_basis R M).eval_range⟩⟩

end is_reflexive

section perfect_pairing

variables (N P : Type*) [add_comm_group N] [module R N] [add_comm_group P] [module R P]

/-- A perfect pairing between two modules `M` and `N` is a bilinear map `M × N → R`
such that the induces maps `M → N*` and `N → M*` are both bijective.

To see that `bijective_flip_to_lin` is necessary, consider the pairing between `dual R M` and
`M` given by the identity map. This satisfies `bijective_flip_to_lin` only if `M` is reflexive. -/
@[protect_proj]
structure perfect_pairing :=
(to_lin : M →ₗ[R] dual R N)
(bijective_to_lin : bijective to_lin)
(bijective_flip_to_lin : bijective to_lin.flip)

namespace perfect_pairing

variables {R M N P} (p : perfect_pairing R M N) (q : perfect_pairing R N P)

protected def symm : perfect_pairing R N M :=
{ to_lin := p.to_lin.flip,
  bijective_to_lin := p.bijective_flip_to_lin,
  bijective_flip_to_lin := by simp only [p.bijective_to_lin, linear_map.flip_flip], }

@[simp] lemma symm_to_lin_eq_flip_to_lin : p.symm.to_lin = p.to_lin.flip := rfl

protected def to_equiv : M ≃ₗ[R] dual R N :=
linear_equiv.of_bijective p.to_lin p.bijective_to_lin

protected def to_equiv' : N ≃ₗ[R] dual R M :=
p.symm.to_equiv

lemma dual_map_flip_to_equiv_trans_to_equiv_symm :
  (p.to_equiv.trans (q.to_equiv.symm).dual_map : M →ₗ[R] dual R (dual R P)).flip =
  (q.to_equiv.symm.trans p.to_equiv' : dual R P →ₗ[R] dual R M) :=
begin
  ext f m,
  simp only [perfect_pairing.to_equiv, perfect_pairing.to_equiv', linear_map.flip_apply,
    linear_equiv.coe_coe, linear_equiv.trans_apply, linear_equiv.of_bijective_apply,
    linear_equiv.dual_map_apply, symm_to_lin_eq_flip_to_lin],
end

protected def trans : perfect_pairing R M (dual R P) :=
{ to_lin := (p.to_equiv.trans (q.to_equiv.symm).dual_map : M →ₗ[R] dual R (dual R P)),
  bijective_to_lin := linear_equiv.bijective _,
  bijective_flip_to_lin :=
    by { rw dual_map_flip_to_equiv_trans_to_equiv_symm, exact linear_equiv.bijective _, }, }

lemma trans_symm_to_lin : (p.trans p.symm).to_lin = dual.eval R M :=
begin
  -- TODO Fix this proof (mostly by adding missing API for `symm` and `trans`)
  ext m f,
  simp only [perfect_pairing.to_equiv, perfect_pairing.symm, perfect_pairing.trans,
    linear_equiv.coe_coe, dual.eval_apply, linear_equiv.trans_apply, linear_equiv.dual_map_apply,
    linear_equiv.of_bijective_apply],
  rw ← p.to_lin.flip_apply,
  let e := linear_equiv.of_bijective p.to_lin.flip p.bijective_flip_to_lin,
  erw e.apply_symm_apply f,
end

protected lemma is_reflexive (p : perfect_pairing R M N) : is_reflexive R M :=
⟨by { rw ← p.trans_symm_to_lin, exact perfect_pairing.bijective_to_lin _, }⟩

protected lemma is_reflexive' (p : perfect_pairing R M N) : is_reflexive R N :=
⟨by { rw ← p.symm.trans_symm_to_lin, exact perfect_pairing.bijective_to_lin _, }⟩

/-- If `N` is reflexive, then a linear equivalence to its dual induces a perfect pairing. -/
def of_is_reflexive' [is_reflexive R N] (B : M ≃ₗ[R] dual R N) :
  perfect_pairing R M N :=
{ to_lin := (B : M →ₗ[R] dual R N),
  bijective_to_lin := B.bijective,
  bijective_flip_to_lin := B.dual_map.bijective.comp $ is_reflexive.bijective_dual_eval R N }

variables (R M)

/-- A reflexive module has a natural perfect pairing with its dual. -/
def of_is_reflexive [is_reflexive R M] : perfect_pairing R M (dual R M) :=
of_is_reflexive' $ eval_equiv' R M

end perfect_pairing

end perfect_pairing

end module
