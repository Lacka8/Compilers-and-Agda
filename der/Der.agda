open import Relation.Binary using(Decidable)
open import Relation.Binary.PropositionalEquality using(_≡_)

module Der {A : Set} (_≟_ : Decidable {A = A} _≡_) where

open import Relation.Binary.PropositionalEquality using(refl)
open import Data.List using(List;[];_∷_)
open import Relation.Nullary using(Dec;yes;no;¬_)
open import Data.Empty using(⊥) renaming (⊥-elim to void)

open import RegEx
open import Match
open import Empty
open import SmartCons (_≟_) 

der : A → RegEx A → RegEx A
der x ∅ = ∅
der x ε = ∅
der x ⟦ c ⟧    with x ≟ c
der x ⟦ .x ⟧ | yes refl = ε
der x ⟦ c ⟧  | no ¬p = ∅
der x (l ∣ r) = (der x l) ∣' (der x r)
der x (l ⨁ r)   with empty l
der x (l ⨁ r) | yes p = ((der x l) ⨁' r) ∣' der x r
der x (l ⨁ r) | no ¬p = ((der x l) ⨁' r)
der x (r *) = (der x r) ⨁' (r *)

derSound : {xs : List A} → (r : RegEx A) → {x : A} → Match (der x r) xs → Match r (x ∷ xs)
derSound ∅ ()
derSound ε ()
derSound         ⟦ c ⟧ {x}  d    with x ≟ c
derSound {[]}    ⟦ x ⟧      _  | yes refl = char
derSound {_ ∷ _} ⟦ c ⟧      () | yes refl
derSound         ⟦ _ ⟧ {_}  ()          | no _
derSound (l ∣ r) {x} d   with decSound (der x l) (der x r) d
derSound (l ∣ r) {x} d | dec1 m = dec1 (derSound l m)
derSound (l ∣ r) {x} d | dec2 m = dec2 (derSound r m)
derSound (l ⨁ r)     d   with empty l
derSound (l ⨁ r) {x} d | yes p   with decSound (der x l ⨁' r) (der x r) d 
derSound (l ⨁ r) {x} d | yes p | (dec1 m)   with conSound (der x l) r m
derSound (l ⨁ r) {x} d | yes p | (dec1 m) | (con s m1 m2) = con (add s) (derSound l {x} m1) m2
derSound (l ⨁ r)     d | yes p | (dec2 m)   with derSound r m
derSound (l ⨁ r)     d | yes p | (dec2 m) | l2 = con emp p l2
derSound (l ⨁ r) {x} d | no ¬p    with conSound (der x l) r d
derSound (l ⨁ r)     d | no ¬p | (con s m1 m2)   with derSound l m1
derSound (l ⨁ r)     d | no ¬p | (con s m1 m2) | p = con (add s) p m2
derSound (r *)   {x} d   with conSound (der x r) (r *) d
derSound (r *)   {x} d | con s m1 m2   with derSound r m1
derSound (r *)   {x} d | con s m1 m2 | p = star (dec2 (con (add s) p m2))

derComp : {xs : List A} → (r : RegEx A) → {c : A} → Match r (c ∷ xs) → Match (der c r) xs
derComp ∅ ()
derComp ε ()
derComp ⟦ x ⟧ char   with x ≟ x
derComp ⟦ x ⟧ char | yes refl = eps
derComp ⟦ x ⟧ char | no ¬p = void (¬p (refl))
derComp (l ∣ r) {x} (dec1 m) = decComp (der x l) (der x r) (dec1 (derComp l m))
derComp (l ∣ r) {x} (dec2 m) = decComp (der x l) (der x r) (dec2 (derComp r m)) 
derComp (l ⨁ r)      m                    with empty l
derComp (l ⨁ r) {x} (con emp m1 m2)     | yes p = decComp (der x l ⨁' r) (der x r) (dec2 (derComp r m2))
derComp (l ⨁ r) {x} (con (add s) m1 m2) | yes p = decComp (der x l ⨁' r) (der x r) (dec1 (conComp (der x l) r (con s (derComp l m1) m2)))
derComp (l ⨁ r)     (con emp m1 m2)     | no ¬p = void (¬p m1)
derComp (l ⨁ r) {x} (con (add s) m1 m2) | no ¬p = conComp (der x l) r (con s (derComp l m1) m2)
derComp (r *)       (star (dec1 ()))
derComp (r *)       (star (dec2 (con emp m1 m2)))     = derComp (r *) m2
derComp (r *)   {x} (star (dec2 (con (add s) m1 m2))) = conComp (der x r) (r *) (con s (derComp r m1) m2)
