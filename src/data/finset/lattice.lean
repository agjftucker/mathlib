/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.finset.fold
import data.multiset.lattice

/-!
# Lattice operations on multisets
-/

variables {α β γ : Type*}

namespace finset
open multiset

/-! ### sup -/
section sup
variables [semilattice_sup_bot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : finset β) (f : β → α) : α := s.fold (⊔) ⊥ f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma sup_def : s.sup f = (s.1.map f).sup := rfl

@[simp] lemma sup_empty : (∅ : finset β).sup f = ⊥ :=
fold_empty

@[simp] lemma sup_insert [decidable_eq β] {b : β} : (insert b s : finset β).sup f = f b ⊔ s.sup f :=
fold_insert_idem

@[simp] lemma sup_singleton {b : β} : ({b} : finset β).sup f = f b :=
sup_singleton

lemma sup_union [decidable_eq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
finset.induction_on s₁ (by rw [empty_union, sup_empty, bot_sup_eq]) $ λ a s has ih,
by rw [insert_union, sup_insert, sup_insert, ih, sup_assoc]

theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a∈s₂, f a = g a) : s₁.sup f = s₂.sup g :=
by subst hs; exact finset.fold_congr hfg

@[simp] lemma sup_le_iff {a : α} : s.sup f ≤ a ↔ (∀b ∈ s, f b ≤ a) :=
begin
  apply iff.trans multiset.sup_le,
  simp only [multiset.mem_map, and_imp, exists_imp_distrib],
  exact ⟨λ k b hb, k _ _ hb rfl, λ k a' b hb h, h ▸ k _ hb⟩,
end

lemma sup_le {a : α} : (∀b ∈ s, f b ≤ a) → s.sup f ≤ a :=
sup_le_iff.2

lemma le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
sup_le_iff.1 (le_refl _) _ hb

lemma sup_mono_fun {g : β → α} (h : ∀b∈s, f b ≤ g b) : s.sup f ≤ s.sup g :=
sup_le (λ b hb, le_trans (h b hb) (le_sup hb))

lemma sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
sup_le $ assume b hb, le_sup (h hb)

@[simp] lemma sup_lt_iff [is_total α (≤)] {a : α} (ha : ⊥ < a) :
  s.sup f < a ↔ (∀b ∈ s, f b < a) :=
by letI := classical.dec_eq β; from
⟨ λh b hb, lt_of_le_of_lt (le_sup hb) h,
  finset.induction_on s (by simp [ha]) (by simp {contextual := tt}) ⟩

lemma comp_sup_eq_sup_comp [semilattice_sup_bot γ] {s : finset β}
  {f : β → α} (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) :
  g (s.sup f) = s.sup (g ∘ f) :=
by letI := classical.dec_eq β; from
finset.induction_on s (by simp [bot]) (by simp [g_sup] {contextual := tt})

lemma comp_sup_eq_sup_comp_of_is_total [is_total α (≤)] {γ : Type} [semilattice_sup_bot γ]
  (g : α → γ) (mono_g : monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
comp_sup_eq_sup_comp g mono_g.map_sup bot

/-- Computating `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
lemma sup_coe {P : α → Prop}
  {Pbot : P ⊥} {Psup : ∀{{x y}}, P x → P y → P (x ⊔ y)}
  (t : finset β) (f : β → {x : α // P x}) :
  (@sup _ _ (subtype.semilattice_sup_bot Pbot Psup) t f : α) = t.sup (λ x, f x) :=
by { classical, rw [comp_sup_eq_sup_comp coe]; intros; refl }

theorem subset_range_sup_succ (s : finset ℕ) : s ⊆ range (s.sup id).succ :=
λ n hn, mem_range.2 $ nat.lt_succ_of_le $ le_sup hn

theorem exists_nat_subset_range (s : finset ℕ) : ∃n : ℕ, s ⊆ range n :=
⟨_, s.subset_range_sup_succ⟩

lemma mem_sup {α β} [decidable_eq β] {s : finset α} {f : α → multiset β}
  {x : β} : x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v :=
begin
  classical,
  apply s.induction_on,
  { simp },
  { intros a s has hxs,
    rw [finset.sup_insert, multiset.sup_eq_union, multiset.mem_union],
    split,
    { intro hxi,
      cases hxi with hf hf,
      { refine ⟨a, _, hf⟩,
        simp only [true_or, eq_self_iff_true, finset.mem_insert] },
      { rcases hxs.mp hf with ⟨v, hv, hfv⟩,
        refine ⟨v, _, hfv⟩,
        simp only [hv, or_true, finset.mem_insert] } },
    { rintros ⟨v, hv, hfv⟩,
      rw [finset.mem_insert] at hv,
      rcases hv with rfl | hv,
      { exact or.inl hfv },
      { refine or.inr (hxs.mpr ⟨v, hv, hfv⟩) } } },
end

lemma sup_subset {α β} [semilattice_sup_bot β] {s t : finset α} (hst : s ⊆ t) (f : α → β) :
  s.sup f ≤ t.sup f :=
by classical;
calc t.sup f = (s ∪ t).sup f : by rw [finset.union_eq_right_iff_subset.mpr hst]
         ... = s.sup f ⊔ t.sup f : by rw finset.sup_union
         ... ≥ s.sup f : le_sup_left

end sup

lemma sup_eq_supr [complete_lattice β] (s : finset α) (f : α → β) : s.sup f = (⨆a∈s, f a) :=
le_antisymm
  (finset.sup_le $ assume a ha, le_supr_of_le a $ le_supr _ ha)
  (supr_le $ assume a, supr_le $ assume ha, le_sup ha)

/-! ### inf -/
section inf
variables [semilattice_inf_top α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : finset β) (f : β → α) : α := s.fold (⊓) ⊤ f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma inf_def : s.inf f = (s.1.map f).inf := rfl

@[simp] lemma inf_empty : (∅ : finset β).inf f = ⊤ :=
fold_empty

lemma le_inf_iff {a : α} : a ≤ s.inf f ↔ ∀b ∈ s, a ≤ f b :=
@sup_le_iff (order_dual α) _ _ _ _ _

@[simp] lemma inf_insert [decidable_eq β] {b : β} : (insert b s : finset β).inf f = f b ⊓ s.inf f :=
fold_insert_idem

@[simp] lemma inf_singleton {b : β} : ({b} : finset β).inf f = f b :=
inf_singleton

lemma inf_union [decidable_eq β] : (s₁ ∪ s₂).inf f = s₁.inf f ⊓ s₂.inf f :=
@sup_union (order_dual α) _ _ _ _ _ _

theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a∈s₂, f a = g a) : s₁.inf f = s₂.inf g :=
by subst hs; exact finset.fold_congr hfg

lemma inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
le_inf_iff.1 (le_refl _) _ hb

lemma le_inf {a : α} : (∀b ∈ s, a ≤ f b) → a ≤ s.inf f :=
le_inf_iff.2

lemma inf_mono_fun {g : β → α} (h : ∀b∈s, f b ≤ g b) : s.inf f ≤ s.inf g :=
le_inf (λ b hb, le_trans (inf_le hb) (h b hb))

lemma inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
le_inf $ assume b hb, inf_le (h hb)

lemma lt_inf_iff [h : is_total α (≤)] {a : α} (ha : a < ⊤) : a < s.inf f ↔ (∀b ∈ s, a < f b) :=
@sup_lt_iff (order_dual α) _ _ _ _ (@is_total.swap α _ h) _ ha

lemma comp_inf_eq_inf_comp [semilattice_inf_top γ] {s : finset β}
  {f : β → α} (g : α → γ) (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) (top : g ⊤ = ⊤) :
  g (s.inf f) = s.inf (g ∘ f) :=
@comp_sup_eq_sup_comp (order_dual α) _ (order_dual γ) _ _ _ _ _ g_inf top

lemma comp_inf_eq_inf_comp_of_is_total [h : is_total α (≤)] {γ : Type} [semilattice_inf_top γ]
  (g : α → γ) (mono_g : monotone g) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
comp_inf_eq_inf_comp g mono_g.map_inf top

/-- Computating `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
lemma inf_coe {P : α → Prop}
  {Ptop : P ⊤} {Pinf : ∀{{x y}}, P x → P y → P (x ⊓ y)}
  (t : finset β) (f : β → {x : α // P x}) :
  (@inf _ _ (subtype.semilattice_inf_top Ptop Pinf) t f : α) = t.inf (λ x, f x) :=
by { classical, rw [comp_inf_eq_inf_comp coe]; intros; refl }

end inf

lemma inf_eq_infi [complete_lattice β] (s : finset α) (f : α → β) : s.inf f = (⨅a∈s, f a) :=
@sup_eq_supr _ (order_dual β) _ _ _

section exists_max_min

variables [linear_order α]
lemma exists_max_image (s : finset β) (f : β → α) (h : s.nonempty) :
  ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
begin
  letI := classical.DLO α,
  cases sup_of_exists_mem (h.image f) with y hy,
  rcases mem_image.mp (mem_of_sup hy) with ⟨x, hx, rfl⟩,
  exact ⟨x, hx, λ x' hx', le_sup_of_mem (mem_image_of_mem f hx') hy⟩,
end

lemma exists_min_image (s : finset β) (f : β → α) (h : s.nonempty) :
  ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
@exists_max_image (order_dual α) β _ s f h

end exists_max_min
end finset

namespace multiset

lemma count_sup [decidable_eq β] (s : finset α) (f : α → multiset β) (b : β) :
  count b (s.sup f) = s.sup (λa, count b (f a)) :=
begin
  letI := classical.dec_eq α,
  refine s.induction _ _,
  { exact count_zero _ },
  { assume i s his ih,
    rw [finset.sup_insert, sup_eq_union, count_union, finset.sup_insert, ih],
    refl }
end

end multiset


section lattice
variables {ι : Type*} {ι' : Sort*} [complete_lattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `supr_eq_supr_finset'` for a version
that works for `ι : Sort*`. -/
lemma supr_eq_supr_finset (s : ι → α) :
  (⨆i, s i) = (⨆t:finset ι, ⨆i∈t, s i) :=
begin
  classical,
  exact le_antisymm
    (supr_le $ assume b, le_supr_of_le {b} $ le_supr_of_le b $ le_supr_of_le
      (by simp) $ le_refl _)
    (supr_le $ assume t, supr_le $ assume b, supr_le $ assume hb, le_supr _ _)
end

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `supr_eq_supr_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
lemma supr_eq_supr_finset' (s : ι' → α) :
  (⨆i, s i) = (⨆t:finset (plift ι'), ⨆i∈t, s (plift.down i)) :=
by rw [← supr_eq_supr_finset, ← equiv.plift.surjective.supr_comp]; refl

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `infi_eq_infi_finset'` for a version
that works for `ι : Sort*`. -/
lemma infi_eq_infi_finset (s : ι → α) :
  (⨅i, s i) = (⨅t:finset ι, ⨅i∈t, s i) :=
@supr_eq_supr_finset (order_dual α) _ _ _

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `infi_eq_infi_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
lemma infi_eq_infi_finset' (s : ι' → α) :
  (⨅i, s i) = (⨅t:finset (plift ι'), ⨅i∈t, s (plift.down i)) :=
@supr_eq_supr_finset' (order_dual α) _ _ _

end lattice

namespace set
variables {ι : Type*} {ι' : Sort*}

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `Union_eq_Union_finset'` for
a version that works for `ι : Sort*`. -/
lemma Union_eq_Union_finset (s : ι → set α) :
  (⋃i, s i) = (⋃t:finset ι, ⋃i∈t, s i) :=
supr_eq_supr_finset s

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `Union_eq_Union_finset` for
a version that assumes `ι : Type*` but avoids `plift`s in the right hand side. -/
lemma Union_eq_Union_finset' (s : ι' → set α) :
  (⋃i, s i) = (⋃t:finset (plift ι'), ⋃i∈t, s (plift.down i)) :=
supr_eq_supr_finset' s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`Inter_eq_Inter_finset'` for a version that works for `ι : Sort*`. -/
lemma Inter_eq_Inter_finset (s : ι → set α) :
  (⋂i, s i) = (⋂t:finset ι, ⋂i∈t, s i) :=
infi_eq_infi_finset s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`Inter_eq_Inter_finset` for a version that assumes `ι : Type*` but avoids `plift`s in the right
hand side. -/
lemma Inter_eq_Inter_finset' (s : ι' → set α) :
  (⋂i, s i) = (⋂t:finset (plift ι'), ⋂i∈t, s (plift.down i)) :=
infi_eq_infi_finset' s

end set

namespace finset

open function

/-! ### Interaction with big lattice/set operations -/

section lattice

lemma supr_coe [has_Sup β] (f : α → β) (s : finset α) :
  (⨆ x ∈ (↑s : set α), f x) = ⨆ x ∈ s, f x :=
rfl

lemma infi_coe [has_Inf β] (f : α → β) (s : finset α) :
  (⨅ x ∈ (↑s : set α), f x) = ⨅ x ∈ s, f x :=
rfl

variables [complete_lattice β]

theorem supr_singleton (a : α) (s : α → β) : (⨆ x ∈ ({a} : finset α), s x) = s a :=
by simp

theorem infi_singleton (a : α) (s : α → β) : (⨅ x ∈ ({a} : finset α), s x) = s a :=
by simp

variables [decidable_eq α]

theorem supr_union {f : α → β} {s t : finset α} :
  (⨆ x ∈ s ∪ t, f x) = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) :=
by simp [supr_or, supr_sup_eq]

theorem infi_union {f : α → β} {s t : finset α} :
  (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ (⨅ x ∈ t, f x) :=
by simp [infi_or, infi_inf_eq]

lemma supr_insert (a : α) (s : finset α) (t : α → β) :
  (⨆ x ∈ insert a s, t x) = t a ⊔ (⨆ x ∈ s, t x) :=
by { rw insert_eq, simp only [supr_union, finset.supr_singleton] }

lemma infi_insert (a : α) (s : finset α) (t : α → β) :
  (⨅ x ∈ insert a s, t x) = t a ⊓ (⨅ x ∈ s, t x) :=
by { rw insert_eq, simp only [infi_union, finset.infi_singleton] }

lemma supr_finset_image {f : γ → α} {g : α → β} {s : finset γ} :
  (⨆ x ∈ s.image f, g x) = (⨆ y ∈ s, g (f y)) :=
by rw [← supr_coe, coe_image, supr_image, supr_coe]

lemma infi_finset_image {f : γ → α} {g : α → β} {s : finset γ} :
  (⨅ x ∈ s.image f, g x) = (⨅ y ∈ s, g (f y)) :=
by rw [← infi_coe, coe_image, infi_image, infi_coe]

lemma supr_insert_update {x : α} {t : finset α} (f : α → β) {s : β} (hx : x ∉ t) :
  (⨆ (i ∈ insert x t), function.update f x s i) = (s ⊔ ⨆ (i ∈ t), f i) :=
begin
  simp only [finset.supr_insert, update_same],
  rcongr i hi, apply update_noteq, rintro rfl, exact hx hi
end

lemma infi_insert_update {x : α} {t : finset α} (f : α → β) {s : β} (hx : x ∉ t) :
  (⨅ (i ∈ insert x t), update f x s i) = (s ⊓ ⨅ (i ∈ t), f i) :=
@supr_insert_update α (order_dual β) _ _ _ _ f _ hx

end lattice

@[simp] theorem bUnion_coe (s : finset α) (t : α → set β) :
  (⋃ x ∈ (↑s : set α), t x) = ⋃ x ∈ s, t x :=
rfl

@[simp] theorem bInter_coe (s : finset α) (t : α → set β) :
  (⋂ x ∈ (↑s : set α), t x) = ⋂ x ∈ s, t x :=
rfl

@[simp] theorem bUnion_singleton (a : α) (s : α → set β) : (⋃ x ∈ ({a} : finset α), s x) = s a :=
supr_singleton a s

@[simp] theorem bInter_singleton (a : α) (s : α → set β) : (⋂ x ∈ ({a} : finset α), s x) = s a :=
infi_singleton a s

@[simp] lemma bUnion_preimage_singleton (f : α → β) (s : finset β) :
  (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' ↑s :=
set.bUnion_preimage_singleton f ↑s

variables [decidable_eq α]

lemma bUnion_union (s t : finset α) (u : α → set β) :
  (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ (⋃ x ∈ t, u x) :=
supr_union

lemma bInter_inter (s t : finset α) (u : α → set β) :
  (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ (⋂ x ∈ t, u x) :=
infi_union

@[simp] lemma bUnion_insert (a : α) (s : finset α) (t : α → set β) :
  (⋃ x ∈ insert a s, t x) = t a ∪ (⋃ x ∈ s, t x) :=
supr_insert a s t

@[simp] lemma bInter_insert (a : α) (s : finset α) (t : α → set β) :
  (⋂ x ∈ insert a s, t x) = t a ∩ (⋂ x ∈ s, t x) :=
infi_insert a s t

@[simp] lemma bUnion_finset_image {f : γ → α} {g : α → set β} {s : finset γ} :
  (⋃x ∈ s.image f, g x) = (⋃y ∈ s, g (f y)) :=
supr_finset_image

@[simp] lemma bInter_finset_image {f : γ → α} {g : α → set β} {s : finset γ} :
  (⋂ x ∈ s.image f, g x) = (⋂ y ∈ s, g (f y)) :=
infi_finset_image

lemma bUnion_insert_update {x : α} {t : finset α} (f : α → set β) {s : set β} (hx : x ∉ t) :
  (⋃ (i ∈ insert x t), @update _ _ _ f x s i) = (s ∪ ⋃ (i ∈ t), f i) :=
supr_insert_update f hx

lemma bInter_insert_update {x : α} {t : finset α} (f : α → set β) {s : set β} (hx : x ∉ t) :
  (⋂ (i ∈ insert x t), @update _ _ _ f x s i) = (s ∩ ⋂ (i ∈ t), f i) :=
infi_insert_update f hx

end finset
