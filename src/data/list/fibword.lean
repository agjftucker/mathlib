/-
Copyright (c) 2020 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/

import data.stream.basic
import data.list.palindrome
open list

/-- Auxiliary function for `fibword_morph`. -/
def fibword_morph_aux : bool → list bool
| ff := [ff, tt]
| tt := [ff]

/-- Fibonacci word morphism. -/
def fibword_morph (l : list bool) : list bool := l.bind fibword_morph_aux

lemma fibword_morph_append {x y} : fibword_morph (x ++ y) = fibword_morph x ++ fibword_morph y :=
by { unfold fibword_morph, rw bind_append }

lemma fibword_morph_cons {x l} : fibword_morph (x :: l) = fibword_morph_aux x ++ fibword_morph l :=
rfl

lemma fibword_morph_nil : fibword_morph [] = [] := rfl

lemma fibword_morph_ne_nil {l} (hne : l ≠ []) : fibword_morph l ≠ [] :=
begin
  induction l with x l h, contradiction,
  rw fibword_morph_cons,
  cases x; trivial
end

/-- The Fibonacci words are formed by repeated applications of the Fibonacci word morphism. -/
def fibword : ℕ → list bool := stream.iterate fibword_morph [ff]

lemma head_fibword_morph {l : list bool} : head (fibword_morph l) = ff :=
begin
  induction l with x l, { refl },
  unfold fibword_morph,
  cases x; rw [cons_bind, fibword_morph_aux, cons_append, head_cons],
end

lemma palindrome_fibword_morph {l : list bool} (p : palindrome l) :
  palindrome (tail (fibword_morph l)) :=
begin
  refine palindrome.rec_on p palindrome.nil _ _,
  -- l = [x]
  { intros x, cases x; exact palindrome.of_reverse_eq rfl },
  -- l = [x, ..., x]
  { intros x l p h,
    unfold fibword_morph,
    rw [cons_bind, bind_append, bind_singleton],
    cases l with y l,
    -- l = [x, x]
    { cases x; { rw fibword_morph_aux, exact palindrome.of_reverse_eq rfl } },
    -- l = [x, y, ..., y, x]
    cases x;
    { rw [fibword_morph_aux, ←fibword_morph,
          ←cons_head_tail (fibword_morph_ne_nil (cons_ne_nil y l)),
          head_fibword_morph],
      apply palindrome.of_reverse_eq,
      simp [h.to_reverse_eq] } }
end
