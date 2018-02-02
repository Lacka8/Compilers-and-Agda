open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using(_≡_;refl;cong)

module SmartCons {A : Set} (_≟_ : Decidable {A = A} _≡_) where

open import Data.List using(List;[];_∷_)

open import RegEx
open import Match

_∣'_ : RegEx{A} → RegEx{A} → RegEx
--∅ ∣' ∅ = ∅
∅ ∣' r = r
r ∣' ∅ = r
l ∣' r = l ∣ r

_⨁'_ : RegEx{A} → RegEx{A} → RegEx
∅ ⨁' _ = ∅
_ ⨁' ∅ = ∅
ε ⨁' r = r
r ⨁' ε = r
l ⨁' r = l ⨁ r

_*' :  RegEx{A} → RegEx
∅ *' = ε
ε *' = ε
r *' = r *

--proofs

decSound : {s : List A} → (l r : RegEx) → Match (l ∣' r) s → Match (l ∣ r) s
decSound ∅ _ x = dec2 x
decSound ε       ∅ x = dec1 x
decSound ⟦ _ ⟧   ∅ x = dec1 x
decSound (_ ∣ _) ∅ x = dec1 x
decSound (_ ⨁ _) ∅ x = dec1 x
decSound (_ *)   ∅ x = dec1 x
decSound ε       ε       x = x
decSound ε       ⟦ _ ⟧   x = x
decSound ε       (_ ∣ _) x = x
decSound ε       (_ ⨁ _) x = x
decSound ε       (_ *)   x = x
decSound ⟦ _ ⟧   ε       x = x
decSound ⟦ _ ⟧   ⟦ _ ⟧   x = x
decSound ⟦ _ ⟧   (_ ∣ _) x = x
decSound ⟦ _ ⟧   (_ ⨁ _) x = x
decSound ⟦ _ ⟧   (_ *)   x = x
decSound (_ ∣ _) ε       x = x
decSound (_ ∣ _) ⟦ _ ⟧   x = x
decSound (_ ∣ _) (_ ∣ _) x = x
decSound (_ ∣ _) (_ ⨁ _) x = x
decSound (_ ∣ _) (_ *)   x = x
decSound (_ ⨁ _) ε       x = x
decSound (_ ⨁ _) ⟦ _ ⟧   x = x
decSound (_ ⨁ _) (_ ∣ _) x = x
decSound (_ ⨁ _) (_ ⨁ _) x = x
decSound (_ ⨁ _) (_ *)   x = x
decSound (_ *)   ε       x = x
decSound (_ *)   ⟦ _ ⟧   x = x
decSound (_ *)   (_ ∣ _) x = x
decSound (_ *)   (_ ⨁ _) x = x
decSound (_ *)   (_ *)   x = x

decComp :{s : List A} → (l r : RegEx) → Match (l ∣ r) s → Match (l ∣' r) s
decComp _ ∅ (dec2 ())
decComp ∅ _ (dec1 ())
decComp ∅ _ (dec2 x) = x
decComp ε       ∅ (dec1 eps)           = eps
decComp (⟦ _ ⟧) ∅ (dec1 char)          = char
decComp (_ ∣ _) ∅ (dec1 (dec1 x))      = dec1 x
decComp (_ ∣ _) ∅ (dec1 (dec2 x))      = dec2 x
decComp (_ ⨁ _) ∅ (dec1 (con s x1 x2)) = con s x1 x2
decComp (_ *)   ∅ (dec1 (star x))      = star x
decComp ε       ε       x = x
decComp ε       ⟦ _ ⟧   x = x
decComp ε       (_ ∣ _) x = x
decComp ε       (_ ⨁ _) x = x
decComp ε       (_ *)   x = x
decComp ⟦ _ ⟧   ε       x = x
decComp ⟦ _ ⟧   ⟦ _ ⟧   x = x
decComp ⟦ _ ⟧   (_ ∣ _) x = x
decComp ⟦ _ ⟧   (_ ⨁ _) x = x
decComp ⟦ _ ⟧   (_ *)   x = x
decComp (_ ∣ _) ε       x = x
decComp (_ ∣ _) ⟦ _ ⟧   x = x
decComp (_ ∣ _) (_ ∣ _) x = x
decComp (_ ∣ _) (_ ⨁ _) x = x
decComp (_ ∣ _) (_ *)   x = x
decComp (_ ⨁ _) ε       x = x
decComp (_ ⨁ _) ⟦ _ ⟧   x = x
decComp (_ ⨁ _) (_ ∣ _) x = x
decComp (_ ⨁ _) (_ ⨁ _) x = x
decComp (_ ⨁ _) (_ *)   x = x
decComp (_ *)   ε       x = x
decComp (_ *)   ⟦ _ ⟧   x = x
decComp (_ *)   (_ ∣ _) x = x
decComp (_ *)   (_ ⨁ _) x = x
decComp (_ *)   (_ *)   x = x

emptySplit : {A : Set} → (s : List A) → Split s s []
emptySplit   []    = emp
emptySplit (_ ∷ s) = add (emptySplit s)

conSound : {s : List A} → (l r : RegEx) → Match (l ⨁' r) s → Match (l ⨁ r) s
conSound ∅       _ ()
conSound ε       ∅ ()
conSound ⟦ _ ⟧   ∅ ()
conSound (_ ∣ _) ∅ ()
conSound (_ ⨁ _) ∅ ()
conSound (_ *)   ∅ ()
conSound ε ε       x = con emp eps x
conSound ε ⟦ _ ⟧   x = con emp eps x
conSound ε (_ ∣ _) x = con emp eps x
conSound ε (_ ⨁ _) x = con emp eps x
conSound ε (_ *)   x = con emp eps x
conSound ⟦ _ ⟧   ε char = con (add emp) char eps
conSound {s} (_ ∣ _) ε x = con (emptySplit s) x eps
conSound {s} (_ ⨁ _) ε x = con (emptySplit s) x eps
conSound {s} (_ *)   ε x = con (emptySplit s) x eps
conSound ⟦ _ ⟧   ⟦ _ ⟧   x = x
conSound ⟦ _ ⟧   (_ ∣ _) x = x
conSound ⟦ _ ⟧   (_ ⨁ _) x = x
conSound ⟦ _ ⟧   (_ *)   x = x
conSound (_ ∣ _) ⟦ _ ⟧   x = x
conSound (_ ∣ _) (_ ∣ _) x = x
conSound (_ ∣ _) (_ ⨁ _) x = x
conSound (_ ∣ _) (_ *)   x = x
conSound (_ ⨁ _) ⟦ _ ⟧   x = x
conSound (_ ⨁ _) (_ ∣ _) x = x
conSound (_ ⨁ _) (_ ⨁ _) x = x
conSound (_ ⨁ _) (_ *)   x = x
conSound (_ *)   ⟦ _ ⟧   x = x
conSound (_ *)   (_ ∣ _) x = x
conSound (_ *)   (_ ⨁ _) x = x
conSound (_ *)   (_ *)   x = x

conεr : {r : RegEx} → {s : List A} →  Match (ε ⨁ r) s → Match r s
conεr (con emp _ x) = x
conεr (con (add _) () _)

splitε : {l1 l2 : List A} → Split l1 l2 [] → l1 ≡ l2
splitε emp = refl
splitε {a ∷ _}(add x) = cong (_∷_ a) (splitε x)

conrε' : {s : List A} → {r : RegEx} →  Match (r ⨁ ε) s → Match r s
conrε' {[]}       (con (emp {.[]}) x _) = x
conrε' {x ∷ xs}   (con (emp {.(x ∷ xs)}) _ ())
conrε' {.(_ ∷ _)} (con {s2 = []}     (add {l2 = .[]}       x) _ eps)    with splitε x
conrε' {.(_ ∷ l)} (con {s2 = []}     (add {l}{.l} {.[]}    _) x eps) | refl = x
conrε' {.(_ ∷ _)} (con {s2 = x ∷ xs} (add {l2 = .(x ∷ xs)} _) _  ())

conComp : {s : List A} → (l r : RegEx) → Match (l ⨁ r) s → Match (l ⨁' r) s
conComp _ ∅       (con _ _ ())
conComp ∅ ε       (con _ () _)
conComp ∅ ⟦ _ ⟧   (con _ () _)
conComp ∅ (_ ∣ _) (con _ () _)
conComp ∅ (_ ⨁ _) (con _ () _)
conComp ∅ (_ *)   (con _ () _)
conComp ε ε       x = conεr x
conComp ε ⟦ _ ⟧   x = conεr x
conComp ε (_ ∣ _) x = conεr x
conComp ε (_ ⨁ _) x = conεr x
conComp ε (_ *)   x = conεr x
conComp ⟦ _ ⟧   ε x = conrε' x
conComp (_ ∣ _) ε x = conrε' x
conComp (_ ⨁ _) ε x = conrε' x
conComp (_ *)   ε x = conrε' x
conComp ⟦ _ ⟧   ⟦ _ ⟧   x = x
conComp ⟦ _ ⟧   (_ ∣ _) x = x
conComp ⟦ _ ⟧   (_ ⨁ _) x = x
conComp ⟦ _ ⟧   (_ *)   x = x
conComp (_ ∣ _) ⟦ _ ⟧   x = x
conComp (_ ∣ _) (_ ∣ _) x = x
conComp (_ ∣ _) (_ ⨁ _) x = x
conComp (_ ∣ _) (_ *)   x = x
conComp (_ ⨁ _) ⟦ _ ⟧   x = x
conComp (_ ⨁ _) (_ ∣ _) x = x
conComp (_ ⨁ _) (_ ⨁ _) x = x
conComp (_ ⨁ _) (_ *)   x = x
conComp (_ *)   ⟦ _ ⟧   x = x
conComp (_ *)   (_ ∣ _) x = x
conComp (_ *)   (_ ⨁ _) x = x
conComp (_ *)   (_ *)   x = x

starSound : {s : List A} → (r : RegEx) → Match (r *') s → Match (r *) s
starSound ∅ x = star (dec1 x)
starSound ε x = star (dec1 x)
starSound ⟦ _ ⟧   x = x
starSound (_ ∣ _) x = x
starSound (_ ⨁ _) x = x
starSound (_ *)   x = x

starComp : {s : List A} → (r : RegEx) → Match (r *) s → Match (r *') s
starComp ∅ (star (dec1 eps)) = eps
starComp ∅ (star (dec2 (con _ () _)))
starComp ε (star (dec1 eps)) = eps
starComp ε (star (dec2 (con emp _ x))) = starComp ε x
starComp ε (star (dec2 (con (add _) () _)))
starComp ⟦ _ ⟧   x = x
starComp (_ ∣ _) x = x
starComp (_ ⨁ _) x = x
starComp (_ *)   x = x
