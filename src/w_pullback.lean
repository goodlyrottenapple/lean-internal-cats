import category_theory.category
import category_theory.limits.limits
import category_theory.limits.shapes

open category_theory
open category_theory.limits

universes v u  -- declare the `v`'s first; see `category_theory.category` for an explanation

local attribute [tidy] tactic.case_bash

@[derive decidable_eq] inductive walking_w : Type v
| left | middle | right | one | two

instance fintype_walking_w : fintype walking_w :=
{ elems := [walking_w.left, walking_w.middle, walking_w.right, walking_w.one, walking_w.two].to_finset,
  complete := λ x, by { cases x; simp } }

namespace walking_w

/-- The arrows in a pullback diagram. -/
inductive hom : walking_w → walking_w → Type v
| inl1 : hom left one
| inr1 : hom middle one
| inl2 : hom middle two
| inr2 : hom right two
| id : Π X : walking_w.{v}, hom X X

open hom

def hom.comp : Π (X Y Z : walking_w) (f : hom X Y) (g : hom Y Z), hom X Z
| _ _ _ (id _) h := h
| _ _ _ inl1    (id one) := inl1
| _ _ _ inr1    (id one) := inr1
| _ _ _ inl2    (id two) := inl2
| _ _ _ inr2    (id two) := inr2
.

instance category_struct : category_struct walking_w :=
{ hom  := hom,
  id   := hom.id,
  comp := hom.comp, }

instance (X Y : walking_w) : subsingleton (X ⟶ Y) := begin tidy end

-- We make this a @[simp] lemma later; if we do it now there's a mysterious
-- failure in `cospan`, below.
lemma hom_id (X : walking_w.{v}) : hom.id X = 𝟙 X := rfl

/-- The walking_cospan is the index diagram for a pullback. -/
instance : small_category.{v} walking_w.{v} := sparse_category

end walking_w


open walking_w walking_w.hom

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
def w_cospan {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) : walking_w.{v} ⥤ C :=
{ obj := λ x, match x with
  | left := X
  | middle := Y
  | right := V
  | one := W
  | two := Z
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, inl1 := f1
  | _, _, inr1 := g1
  | _, _, inl2 := f2
  | _, _, inr2 := g2
  end }


@[simp] lemma w_cospan_left {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).obj walking_w.left = X := rfl

@[simp] lemma w_cospan_middle {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).obj walking_w.middle = Y := rfl

@[simp] lemma w_cospan_right {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).obj walking_w.right = V := rfl


@[simp] lemma w_cospan_one {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).obj walking_w.one = W := rfl

@[simp] lemma w_cospan_two {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).obj walking_w.two = Z := rfl

  
@[simp] lemma w_cospan_map_inl1 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).map walking_w.hom.inl1 = f1 := rfl

@[simp] lemma w_cospan_map_inr1 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).map walking_w.hom.inr1 = g1 := rfl


@[simp] lemma w_cospan_map_inl2 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).map walking_w.hom.inl2 = f2 := rfl

@[simp] lemma w_cospan_map_inr2 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).map walking_w.hom.inr2 = g2 := rfl


@[simp] lemma w_cospan_map_id1 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) (w : walking_w) :
  (w_cospan f1 g1 f2 g2).map (walking_w.hom.id w) = 𝟙 _ := rfl


variables {X Y V W Z : C}

attribute [simp] walking_w.hom_id

abbreviation w_pullback_cone (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) := cone (w_cospan f1 g1 f2 g2)


namespace w_pullback_cone
variables {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z}

abbreviation fst (t : w_pullback_cone f1 g1 f2 g2) : t.X ⟶ X := t.π.app left
abbreviation mid (t : w_pullback_cone f1 g1 f2 g2) : t.X ⟶ Y := t.π.app middle
abbreviation snd (t : w_pullback_cone f1 g1 f2 g2) : t.X ⟶ V := t.π.app right

def mk {P : C} (fst : P ⟶ X) (mid : P ⟶ Y) (snd : P ⟶ V) (eq1 : fst ≫ f1 = mid ≫ g1) (eq2 : mid ≫ f2 = snd ≫ g2) : w_pullback_cone f1 g1 f2 g2 :=
{ X := P,
  π := 
  { app := λ j, walking_w.cases_on j fst mid snd (fst ≫ f1) (mid ≫ f2),
    naturality' := λ j j' f, begin cases f; obviously end } }

end w_pullback_cone



abbreviation w_pullback {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) [has_limit (w_cospan f1 g1 f2 g2)] :=
limit (w_cospan f1 g1 f2 g2)

abbreviation w_pullback.fst {X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)] : w_pullback f1 g1 f2 g2 ⟶ X :=
limit.π (w_cospan f1 g1 f2 g2) walking_w.left
abbreviation w_pullback.mid {X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)] : w_pullback f1 g1 f2 g2 ⟶ Y :=
limit.π (w_cospan f1 g1 f2 g2) walking_w.middle
abbreviation w_pullback.snd {X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)] : w_pullback f1 g1 f2 g2 ⟶ V :=
limit.π (w_cospan f1 g1 f2 g2) walking_w.right

abbreviation w_pullback.lift {P X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)]
  (h : P ⟶ X) (j : P ⟶ Y) (k : P ⟶ V) (w1 : h ≫ f1 = j ≫ g1) (w2 : j ≫ f2 = k ≫ g2) : P ⟶ w_pullback f1 g1 f2 g2 :=
limit.lift _ (w_pullback_cone.mk h j k w1 w2)


lemma w_pullback.condition1 {X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)] :
  (w_pullback.fst : w_pullback f1 g1 f2 g2 ⟶ X) ≫ f1 = w_pullback.mid ≫ g1 :=
(limit.w (w_cospan f1 g1 f2 g2) walking_w.hom.inl1).trans
(limit.w (w_cospan f1 g1 f2 g2) walking_w.hom.inr1).symm


lemma w_pullback.condition2 {X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)] :
  (w_pullback.mid : w_pullback f1 g1 f2 g2 ⟶ Y) ≫ f2 = w_pullback.snd ≫ g2 :=
(limit.w (w_cospan f1 g1 f2 g2) walking_w.hom.inl2).trans
(limit.w (w_cospan f1 g1 f2 g2) walking_w.hom.inr2).symm


lemma w_pullback.condition2' {X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)] :
  (w_pullback.snd : w_pullback f1 g1 f2 g2 ⟶ V) ≫ g2 = w_pullback.mid ≫ f2 :=
by simp[w_pullback.condition2]

