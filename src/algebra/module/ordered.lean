/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.module.basic
import algebra.ordered_group

set_option default_priority 100 -- see Note [default priority]

/--
An ordered semimodule is an ordered additive commutative monoid
with a partial order in which the scalar multiplication is compatible with the order.
-/
@[protect_proj, ancestor ordered_add_comm_group semimodule]
class ordered_semimodule (R β : Type*)
  [ordered_semiring R] [ordered_add_comm_monoid β] extends semimodule R β :=
(smul_lt_smul_of_pos : ∀ a b : β, a < b → ∀ c : R, 0 < c → c • a < c • b)
(lt_of_smul_lt_smul_of_nonneg : ∀ a b : β, ∀ c : R, c • a < c • b → 0 ≤ c → a < b)

variable {R : Type*}

instance linear_ordered_ring.to_ordered_semimodule [linear_ordered_ring R] :
  ordered_semimodule R R :=
{ smul_lt_smul_of_pos      := λ _ _ hab _ hc, ordered_semiring.mul_lt_mul_of_pos_left _ _ _ hab hc,
  lt_of_smul_lt_smul_of_nonneg  := λ _ _ _ hc h, lt_of_mul_lt_mul_left hc h }

variables {β : Type*} [linear_ordered_ring R] [ordered_add_comm_monoid β] [ordered_semimodule R β]
  {a b : β} {c : R}

lemma smul_lt_smul_of_nonneg (h₁ : a < b) (h₂ : 0 < c) : c • a < c • b :=
  ordered_semimodule.smul_lt_smul_of_pos a b h₁ c h₂

lemma smul_le_smul_of_nonneg (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b :=
begin
  by_cases H₁ : c = 0,
  { simp [H₁, zero_smul] },
  { by_cases H₂ : a = b,
    { rw H₂ },
    { exact le_of_lt
        (smul_lt_smul_of_nonneg (lt_of_le_of_ne h₁ H₂) (lt_of_le_of_ne h₂ (ne.symm H₁))), } }
end
