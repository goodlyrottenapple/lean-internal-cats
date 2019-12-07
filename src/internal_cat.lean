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


@[simp] lemma cospan_one {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).obj walking_w.one = W := rfl

@[simp] lemma cospan_two {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).obj walking_w.two = Z := rfl

  
@[simp] lemma cospan_map_inl1 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).map walking_w.hom.inl1 = f1 := rfl

@[simp] lemma cospan_map_inr1 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).map walking_w.hom.inr1 = g1 := rfl


@[simp] lemma cospan_map_inl2 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).map walking_w.hom.inl2 = f2 := rfl

@[simp] lemma cospan_map_inr2 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) :
  (w_cospan f1 g1 f2 g2).map walking_w.hom.inr2 = g2 := rfl


@[simp] lemma cospan_map_id1 {X Y V W Z : C} (f1 : X ⟶ W) (g1 : Y ⟶ W) (f2 : Y ⟶ Z) (g2 : V ⟶ Z) (w : walking_w) :
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






class internal_category [category.{v} C] [limits.has_limits.{v} C] (obj_obj : C) : Type (max v u) :=
    (obj_arr          : C) 
    (i                : obj_obj ⟶ obj_arr)
    (dom              : obj_arr ⟶ obj_obj)
    (cod              : obj_arr ⟶ obj_obj)
    (notation `a2`    := pullback cod dom)
    (comp             : a2 ⟶ obj_arr)
    (notation `π1`    := @pullback.fst _ _ _ _ _ cod dom _)
    (notation `π2`    := @pullback.snd _ _ _ _ _ cod dom _)
    (dom_comp         : comp ≫ dom = π1 ≫ dom)
    (cod_comp         : comp ≫ cod = π2 ≫ cod)
    (dom_i_id         : i ≫ dom = 𝟙 obj_obj)
    (cod_i_id         : i ≫ cod = 𝟙 obj_obj)
    (comp_dom_id      : (pullback.lift (dom ≫ i) (𝟙 obj_arr) (by simp [cod_i_id])) ≫ comp = 𝟙 obj_arr)
    (comp_cod_id      : (pullback.lift (𝟙 obj_arr) (cod ≫ i) (by simp [dom_i_id])) ≫ comp = 𝟙 obj_arr)
    (notation `left`  := @pullback.fst _ _ _ _ _ π2 π1 _)
    (notation `right` := @pullback.snd _ _ _ _ _ π2 π1 _)
    (notation `compl` := pullback.lift (left ≫ comp) (right ≫ π2) 
        (begin 
            simp [cod_comp, pullback.condition], 
            rw category.assoc_symm, 
            simp [pullback.condition]
        end))
    (notation `compr` := pullback.lift (left ≫ π1) (right ≫ comp) 
        (begin 
            simp [dom_comp, pullback.condition], 
            rw category.assoc_symm, 
            simp [pullback.condition]
        end))
    (comp_compl_compr : compl ≫ comp = compr ≫ comp)

set_option trace.check true



lemma pullback_one_eq_f_fst {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)] : 
    (pullback.fst : pullback f g ⟶ X) ≫ f = ((limit.cone (cospan f g)).π).app walking_cospan.one := by apply (limit.w (cospan f g) walking_cospan.hom.inl)



lemma w_pullback_one_eq_f1_fst {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)] : 
    (w_pullback.fst : w_pullback f1 g1 f2 g2 ⟶ X) ≫ f1 = ((limit.cone (w_cospan f1 g1 f2 g2)).π).app walking_w.one := by apply (limit.w (w_cospan f1 g1 f2 g2) walking_w.hom.inl1)

lemma w_pullback_two_eq_f2_fst {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)] : 
    (w_pullback.mid : w_pullback f1 g1 f2 g2 ⟶ Y) ≫ f2 = ((limit.cone (w_cospan f1 g1 f2 g2)).π).app walking_w.two := by apply (limit.w (w_cospan f1 g1 f2 g2) walking_w.hom.inl2)



lemma pullback_unique_morphism {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)]
  {h h' : W ⟶ pullback f g} (eq_left : h ≫ pullback.fst = h' ≫ pullback.fst) (eq_right : h ≫ pullback.snd = h' ≫ pullback.snd) : h = h' := 
begin
    apply is_limit.hom_ext,
    apply has_limit.is_limit,
    intros w,
    cases w,
    simp[eq_left],
    simp[eq_right],
    rw ← pullback_one_eq_f_fst,
    rw category.assoc_symm, 
    rw category.assoc_symm, 
    simp[eq_left]
end




lemma w_pullback_unique_morphism {P X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)]
  {h h' : P ⟶ w_pullback f1 g1 f2 g2} 
  (eq_left : h ≫ w_pullback.fst = h' ≫ w_pullback.fst) 
  (eq_mid : h ≫ w_pullback.mid = h' ≫ w_pullback.mid) 
  (eq_right : h ≫ w_pullback.snd = h' ≫ w_pullback.snd) : 
  h = h' := 
begin
    apply is_limit.hom_ext,
    apply has_limit.is_limit,
    intros w, cases w,
    simp[eq_left],
    simp[eq_mid],
    simp[eq_right],
    rw ← w_pullback_one_eq_f1_fst,
    rw category.assoc_symm, 
    rw category.assoc_symm, 
    simp[eq_left],
    rw ← w_pullback_two_eq_f2_fst,
    rw category.assoc_symm, 
    rw category.assoc_symm, 
    simp[eq_mid]
end



lemma obv_l {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)] (l : W ⟶ X) (r : W ⟶ Y) (prf : l ≫ f = r ≫ g) : 
    (@pullback.lift C _ W X Y Z f g _ l r prf) ≫ pullback.fst = l := begin simp, apply rfl end

lemma obv_r {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)] (l : W ⟶ X) (r : W ⟶ Y) (prf : l ≫ f = r ≫ g) : 
    (@pullback.lift C _ W X Y Z f g _ l r prf) ≫ pullback.snd = r := begin simp, apply rfl end




lemma w_obv_l {P X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)]
    (h : P ⟶ X) (j : P ⟶ Y) (k : P ⟶ V) (w1 : h ≫ f1 = j ≫ g1) (w2 : j ≫ f2 = k ≫ g2) : 
    (@w_pullback.lift C _ P X Y V W Z f1 g1 f2 g2 _ h j k w1 w2) ≫ w_pullback.fst = h := begin simp, apply rfl end


lemma w_obv_m {P X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)]
    (h : P ⟶ X) (j : P ⟶ Y) (k : P ⟶ V) (w1 : h ≫ f1 = j ≫ g1) (w2 : j ≫ f2 = k ≫ g2) : 
    (@w_pullback.lift C _ P X Y V W Z f1 g1 f2 g2 _ h j k w1 w2) ≫ w_pullback.mid = j := begin simp, apply rfl end


lemma w_obv_r {P X Y V W Z : C} {f1 : X ⟶ W} {g1 : Y ⟶ W} {f2 : Y ⟶ Z} {g2 : V ⟶ Z} [has_limit (w_cospan f1 g1 f2 g2)]
    (h : P ⟶ X) (j : P ⟶ Y) (k : P ⟶ V) (w1 : h ≫ f1 = j ≫ g1) (w2 : j ≫ f2 = k ≫ g2) : 
    (@w_pullback.lift C _ P X Y V W Z f1 g1 f2 g2 _ h j k w1 w2) ≫ w_pullback.snd = k := begin simp, apply rfl end


lemma comp_left_cong {a b : X ⟶ Y} {c : Y ⟶ Z} {eq : a = b} : a ≫ c = b ≫ c := congr_fun (congr_arg category_struct.comp eq) c


abbreviation X₁ {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) := w_pullback j iC.dom iC.cod j
abbreviation C₁ {C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] := iC.obj_arr

abbreviation domX {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) : (X₁ j) ⟶ X₀ := w_pullback.fst
abbreviation codX {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) : (X₁ j) ⟶ X₀ := w_pullback.snd
abbreviation j₁ {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) : (X₁ j) ⟶ C₁ := w_pullback.mid

abbreviation X₂ {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) := pullback (codX j) (domX j)
abbreviation C₂ {C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] := pullback iC.cod iC.dom

abbreviation πX₁ {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) : (X₂ j) ⟶ (X₁ j) := pullback.fst
abbreviation πX₂ {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) : (X₂ j) ⟶ (X₁ j) := pullback.snd
abbreviation j₂ {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) : (X₂ j) ⟶ C₂ := 
  pullback.lift (pullback.fst ≫ w_pullback.mid) (pullback.snd ≫ w_pullback.mid) (
    begin 
        simp[w_pullback.condition2], 
        rw ← w_pullback.condition1, 
        rw category.assoc_symm, 
        rw pullback.condition,
        simp
    end)

abbreviation iX {X₀ C₀ : C} [limits.has_limits.{v} C] [iC : internal_category C₀] (j : X₀ ⟶ C₀) : X₀ ⟶ (X₁ j) := 
    w_pullback.lift (𝟙 X₀) (j ≫ iC.i) (𝟙 X₀) (by simp[iC.dom_i_id]) (by simp[iC.cod_i_id])


lemma lem_8_4 [has_lim : limits.has_limits.{v} C] {X₀ C₀ : C} [iC : internal_category C₀] (j : X₀ ⟶ C₀)
    {T U : C} {f₁ f₂ : T ⟶ X₁ j} {f₁' f₂' : U ⟶ C₁} 
    {k : T ⟶ U} 
    (dom_cod_X : f₁ ≫ codX j = f₂ ≫ domX j)
    (dom_cod_C : f₁' ≫ iC.cod = f₂' ≫ iC.dom)
    (j_f_1 : f₁ ≫ j₁ j = k ≫ f₁')
    (j_f_2 : f₂ ≫ j₁ j = k ≫ f₂') :
    k ≫ (pullback.lift f₁' f₂' dom_cod_C) = (pullback.lift f₁ f₂ dom_cod_X) ≫ j₂ j := 
begin
    apply pullback_unique_morphism,
    rw ← category.assoc_symm,
    rw obv_l,
    rw ← j_f_1,
    rw ← category.assoc_symm,
    rw obv_l,
    rw category.assoc_symm,
    rw obv_l,

    rw ← category.assoc_symm,
    rw obv_r,
    rw ← j_f_2,
    rw ← category.assoc_symm,
    rw obv_r,
    rw category.assoc_symm,
    rw obv_r
end


instance pulled_back_internal_category.internal_category [has_lim : limits.has_limits.{v} C] (obj_obj X : C) [iC : internal_category obj_obj] (j : X ⟶ obj_obj) :
  internal_category X := { 
      obj_arr := X₁ j ,
      dom := domX j,
      cod := codX j,
      comp := w_pullback.lift 
        (πX₁ j ≫ domX j)
        ((j₂ j) ≫ iC.comp)
        (πX₂ j ≫ codX j) 
        (begin 
            simp[w_pullback.condition1],
            rw iC.dom_comp,
            rw category.assoc_symm,
            rw category.assoc_symm,
            apply comp_left_cong,
            rw (obv_l iC.cod iC.dom (pullback.fst ≫ w_pullback.mid) (pullback.snd ≫ w_pullback.mid)),   
        end)
        (begin 
            simp[w_pullback.condition2'],
            rw iC.cod_comp,
            rw category.assoc_symm,
            rw category.assoc_symm,
            apply comp_left_cong,
            rw (obv_r iC.cod iC.dom (pullback.fst ≫ w_pullback.mid) (pullback.snd ≫ w_pullback.mid))
        end),
      i := iX j,
      dom_comp := by simp[w_obv_l],
      cod_comp := by simp[w_obv_r],
      dom_i_id := by simp[w_obv_l],
      cod_i_id := by simp[w_obv_r],
      comp_dom_id := begin 
          apply w_pullback_unique_morphism,
          work_on_goal 2 { 
              rw ← category.assoc_symm,
              rw (w_obv_r _ _ (pullback.snd ≫ w_pullback.snd)),
              rw category.assoc_symm,
              rw obv_r
          },
          work_on_goal 0 {
              rw ← category.assoc_symm,
              rw w_obv_l,
              rw category.assoc_symm,
              rw obv_l,
              rw ← category.assoc_symm,
              rw w_obv_l,
              simp
          },
          rw ← category.assoc_symm,
          rw w_obv_m,
          rw category.assoc_symm,
          transitivity (j₁ j ≫ pullback.lift (iC.dom ≫ iC.i) (𝟙 C₁) _) ≫ iC.comp,
          apply comp_left_cong,
          symmetry,
          apply lem_8_4,
          rw ← category.assoc_symm,
          rw w_obv_m,
          rw category.assoc_symm,
          simp [w_pullback.condition1],
          simp,
          rw ← category.assoc_symm,
          simp[iC.cod_i_id],
          rw ← category.assoc_symm,
          simp[iC.comp_dom_id]
       end,
      comp_cod_id := begin 
          apply w_pullback_unique_morphism,
          work_on_goal 2 { 
              rw ← category.assoc_symm,
              rw (w_obv_r _ _ (pullback.snd ≫ w_pullback.snd)),
              rw category.assoc_symm,
              rw obv_r,
              simp[w_obv_r]
          },
          work_on_goal 0 {
              rw ← category.assoc_symm,
              rw (w_obv_l _ _ (pullback.snd ≫ w_pullback.snd)),
              rw category.assoc_symm,
              rw obv_l
          },
          rw ← category.assoc_symm,
          rw w_obv_m,
          rw category.assoc_symm,
          transitivity (j₁ j ≫ pullback.lift (𝟙 C₁) (iC.cod ≫ iC.i) _) ≫ iC.comp,
          apply comp_left_cong,
          symmetry,
          apply lem_8_4,
          simp,
          rw ← category.assoc_symm,
          rw w_obv_m,
          rw category.assoc_symm,
          simp [w_pullback.condition2'],
          rw ← category.assoc_symm,
          simp[iC.dom_i_id],
          rw ← category.assoc_symm,
          simp[iC.comp_cod_id]
       end,
      comp_compl_compr := {!!}
  }

