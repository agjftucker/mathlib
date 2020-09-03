/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.multiset.finset_ops
import data.multiset.fold

/-!
# Lattice operations on multisets
-/

namespace multiset
variables {α : Type*}

/-! ### sup -/
section sup
variables [semilattice_sup_bot α]

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
def sup (s : multiset α) : α := s.fold (⊔) ⊥

@[simp] lemma sup_zero : (0 : multiset α).sup = ⊥ :=
fold_zero _ _

@[simp] lemma sup_cons (a : α) (s : multiset α) :
  (a :: s).sup = a ⊔ s.sup :=
fold_cons_left _ _ _ _

@[simp] lemma sup_singleton {a : α} : (a::0).sup = a := by simp

@[simp] lemma sup_add (s₁ s₂ : multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup :=
eq.trans (by simp [sup]) (fold_add _ _ _ _ _)

lemma sup_le {s : multiset α} {a : α} : s.sup ≤ a ↔ (∀b ∈ s, b ≤ a) :=
multiset.induction_on s (by simp)
  (by simp [or_imp_distrib, forall_and_distrib] {contextual := tt})

lemma le_sup {s : multiset α} {a : α} (h : a ∈ s) : a ≤ s.sup :=
sup_le.1 (le_refl _) _ h

lemma sup_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₁.sup ≤ s₂.sup :=
sup_le.2 $ assume b hb, le_sup (h hb)

variables [decidable_eq α]

@[simp] lemma sup_erase_dup (s : multiset α) : (erase_dup s).sup = s.sup :=
fold_erase_dup_idem _ _ _

@[simp] lemma sup_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup :=
by rw [← sup_erase_dup, erase_dup_ext.2, sup_erase_dup, sup_add]; simp

@[simp] lemma sup_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).sup = s₁.sup ⊔ s₂.sup :=
by rw [← sup_erase_dup, erase_dup_ext.2, sup_erase_dup, sup_add]; simp

@[simp] lemma sup_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).sup = a ⊔ s.sup :=
by rw [← sup_erase_dup, erase_dup_ext.2, sup_erase_dup, sup_cons]; simp

end sup

/-! ### inf -/
section inf
variables [semilattice_inf_top α]

/-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/
def inf (s : multiset α) : α := s.fold (⊓) ⊤

@[simp] lemma inf_zero : (0 : multiset α).inf = ⊤ :=
fold_zero _ _

@[simp] lemma inf_cons (a : α) (s : multiset α) :
  (a :: s).inf = a ⊓ s.inf :=
fold_cons_left _ _ _ _

@[simp] lemma inf_singleton {a : α} : (a::0).inf = a := by simp

@[simp] lemma inf_add (s₁ s₂ : multiset α) : (s₁ + s₂).inf = s₁.inf ⊓ s₂.inf :=
eq.trans (by simp [inf]) (fold_add _ _ _ _ _)

lemma le_inf {s : multiset α} {a : α} : a ≤ s.inf ↔ (∀b ∈ s, a ≤ b) :=
multiset.induction_on s (by simp)
  (by simp [or_imp_distrib, forall_and_distrib] {contextual := tt})

lemma inf_le {s : multiset α} {a : α} (h : a ∈ s) : s.inf ≤ a :=
le_inf.1 (le_refl _) _ h

lemma inf_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₂.inf ≤ s₁.inf :=
le_inf.2 $ assume b hb, inf_le (h hb)

variables [decidable_eq α]

@[simp] lemma inf_erase_dup (s : multiset α) : (erase_dup s).inf = s.inf :=
fold_erase_dup_idem _ _ _

@[simp] lemma inf_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).inf = s₁.inf ⊓ s₂.inf :=
by rw [← inf_erase_dup, erase_dup_ext.2, inf_erase_dup, inf_add]; simp

@[simp] lemma inf_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).inf = s₁.inf ⊓ s₂.inf :=
by rw [← inf_erase_dup, erase_dup_ext.2, inf_erase_dup, inf_add]; simp

@[simp] lemma inf_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).inf = a ⊓ s.inf :=
by rw [← inf_erase_dup, erase_dup_ext.2, inf_erase_dup, inf_cons]; simp

end inf

section sup'
variable [semilattice_sup α]

--based on finset.max_of_mem
theorem sup_of_mem {s : multiset α} {a : α} (h : a ∈ s) :
  ∃ b : α, @sup (with_bot α) _ (map coe s) = ↑b :=
(@le_sup (with_bot α) _ _ _ (mem_map_of_mem _ h) _ rfl).imp $ λ b, Exists.fst

--based on finset.max_of_nonempty
theorem sup_of_exists_mem {s : multiset α} (h : ∃ a, a ∈ s) :
  ∃ b : α, @sup (with_bot α) _ (map coe s) = ↑b :=
let ⟨a, ha⟩ := h in sup_of_mem ha

--based on finset.max_eq_none
theorem sup_eq_bot {s : multiset α} : @sup (with_bot α) _ (map coe s) = ⊥ ↔ s = 0 :=
⟨λ h, s.eq_zero_or_exists_mem.elim id
  (λ H, let ⟨a, ha⟩ := sup_of_exists_mem H in by rw h at ha; cases ha),
  λ h, h.symm ▸ sup_zero⟩

--based on finset.le_max_of_mem
theorem le_sup_of_mem {s : multiset α} {a b : α} (h₁ : a ∈ s)
  (h₂ : @sup (with_bot α) _ (map coe s) = ↑b) : a ≤ b :=
by rcases @le_sup (with_bot α) _ _ _ (mem_map_of_mem _ h₁) _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

--based on finset.max'
def sup' (s : multiset α) (H : ∃ k, k ∈ s) : α :=
option.get $ let ⟨k, hk⟩ := H in option.is_some_iff_exists.2 (sup_of_mem hk)

variable (s : multiset α)

--based on finset.le_max'
theorem le_sup' (x) (H2 : x ∈ s) : x ≤ s.sup' ⟨x, H2⟩ :=
le_sup_of_mem H2 $ option.get_mem _

--based on finset.max'_singleton
@[simp] lemma sup'_singleton (a : α) : (a::0).sup' ⟨a, or.inl rfl⟩ = a :=
by simp [sup']

end sup'

section inf'
variable [semilattice_inf α]

theorem inf_of_mem {s : multiset α} {a : α} (h : a ∈ s) :
  ∃ b : α, @inf (with_top α) _ (map coe s) = ↑b :=
@sup_of_mem (order_dual α) _ _ _ h

theorem inf_of_exists_mem {s : multiset α} (h : ∃ a, a ∈ s) :
  ∃ b : α, @inf (with_top α) _ (map coe s) = ↑b :=
@sup_of_exists_mem (order_dual α) _ _ h

theorem inf_eq_top {s : multiset α} : @inf (with_top α) _ (map coe s) = ⊤ ↔ s = 0 :=
@sup_eq_bot (order_dual α) _ _

theorem inf_le_of_mem {s : multiset α} {a b : α} (h₁ : b ∈ s)
  (h₂ : @inf (with_top α) _ (map coe s) = ↑a) : a ≤ b :=
@le_sup_of_mem (order_dual α) _ _ _ _ h₁ h₂

def inf' (s : multiset α) (H : ∃ k, k ∈ s) : α :=
@sup' (order_dual α) _ s H

variable (s : multiset α)

theorem inf'_le (x) (H2 : x ∈ s) : s.inf' ⟨x, H2⟩ ≤ x :=
@le_sup' (order_dual α) _ s x H2

@[simp] lemma inf'_singleton (a : α) : (a::0).inf' ⟨a, or.inl rfl⟩ = a :=
@sup'_singleton (order_dual α) _ a

end inf'

section max_min
variables [decidable_linear_order α]

--based on finset.mem_of_max
theorem mem_of_sup {s : multiset α} : ∀ {a : α}, @sup (with_bot α) _ (map coe s) = ↑a → a ∈ s :=
multiset.induction_on s (λ _ H, by cases H) $
  λ b s (ih : ∀ {a}, (map coe s).sup = ↑a → a ∈ s) a (h : (map coe (b::s)).sup = ↑a),
  begin
    by_cases p : b = a,
    { induction p, exact mem_cons_self b s },
    { cases option.lift_or_get_choice max_choice ↑b (map coe s).sup with q q;
      change @has_sup.sup (with_bot α) _ ↑b (map coe s).sup = _ at q;
      rw [map_cons, sup_cons, q] at h,
      { cases h, cases p rfl },
      { exact mem_cons_of_mem (ih h) } }
  end

theorem mem_of_inf {s : multiset α} : ∀ {a : α}, @inf (with_top α) _ (map coe s) = ↑a → a ∈ s :=
@mem_of_sup (order_dual α) _ _

variables (s : multiset α) (H : ∃ a : α, a ∈ s)

--based on finset.max'_mem
theorem sup'_mem : s.sup' H ∈ s :=
mem_of_sup $ by rw [sup', ←with_bot.some_eq_coe, option.some_get]

theorem inf'_mem : s.inf' H ∈ s :=
@sup'_mem (order_dual α) _ s H

end max_min

end multiset
