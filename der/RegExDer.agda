module RegExDer where

--http://homepages.dcc.ufmg.br/~camarao/certified-parsing-regex.pdf

open import Data.Char using(Char;_≟_)
open import Data.List using(List;[];_∷_;[_];_++_;length;take)
open import Relation.Binary.PropositionalEquality using(_≡_;refl;cong;trans)
open import Relation.Nullary using(Dec;yes;no;¬_)
open import Data.Sum using(_⊎_) renaming(inj₁ to inj1;inj₂ to inj2)
open import Data.Empty using(⊥)
open import Data.String using(toList)
open import Data.Product using(_×_;Σ;_,_) renaming(proj₁ to proj1;proj₂ to proj2)
open import Data.Nat using (ℕ;suc;zero;_≤_;z≤n;s≤s)
open import Data.Maybe using(Maybe;just;nothing)

data RegEx : Set where
 ∅    : RegEx
 ε    : RegEx
 ⟦_⟧  : Char  → RegEx
 _∣_  : RegEx → RegEx → RegEx
 _∪_  : RegEx → RegEx → RegEx
 _*   : RegEx → RegEx

data Split {A : Set}: List A → List A → List A → Set where
 emp : {l : List A} → Split l [] l
 add : {l l1 l2 : List A}{a : A} → Split l l1 l2 → Split (a ∷ l) (a ∷ l1) l2

data Match : RegEx → List Char → Set where
 eps  : Match ε []
 char : {c : Char} → Match ⟦ c ⟧ [ c ]
 dec1 : {l r : RegEx}{s : List Char} → Match l s → Match (l ∣ r) s 
 dec2 : {l r : RegEx}{s : List Char} → Match r s → Match (l ∣ r) s 
 con  : {l r : RegEx}{s s1 s2 : List Char} → Split s s1 s2 → Match l s1 → Match  r s2 → Match (l ∪ r) s
 star : {r : RegEx}{s : List Char} → Match (ε ∣ (r ∪ (r *))) s → Match (r *) s

empty∣ :{l r : RegEx} → ¬ Match l [] → ¬ Match r [] → ¬ Match (l ∣ r) []
empty∣ p1 p2 (dec1 x2) = p1 x2
empty∣ p1 p2 (dec2 x2) = p2 x2

empty∪1 :{l r : RegEx} → ¬ Match l [] →  ¬ Match (l ∪ r) [] 
empty∪1 p (con emp m1 m2) = p m1

empty∪2 :{l r : RegEx} → ¬ Match r [] →  ¬ Match (l ∪ r) [] 
empty∪2 p (con emp m1 m2) = p m2

empty : (r : RegEx) → Dec (Match r [])
empty ∅ = no (λ ())
empty ε = yes eps
empty ⟦ c ⟧ = no (λ ())
empty (l ∣ r)   with empty l | empty r
empty (l ∣ r) | yes p        | p2       = yes (dec1 p)
empty (l ∣ r) | no ¬p        | yes p  = yes (dec2 p)
empty (l ∣ r) | no ¬p        | no ¬p1 = no (empty∣ ¬p ¬p1)
empty (l ∪ r)   with empty l | empty r
empty (l ∪ r) | yes p1       | yes p2 = yes (con emp p1 p2)
empty (l ∪ r) | yes p1       | no ¬p2 = no (empty∪2 ¬p2)
empty (l ∪ r) | no ¬p1       | p2     = no (empty∪1 ¬p1)
empty (r *) = yes (star (dec1 eps))

_∣'_ : RegEx → RegEx → RegEx
--∅ ∣' ∅ = ∅
∅ ∣' r = r
r ∣' ∅ = r
l ∣' r = l ∣ r

_∪'_ : RegEx → RegEx → RegEx
∅ ∪' _ = ∅
_ ∪' ∅ = ∅
ε ∪' r = r
r ∪' ε = r
l ∪' r = l ∪ r

_*' : RegEx → RegEx
∅ *' = ε
ε *' = ε
r *' = r *

decSound : {s : List Char} → (l r : RegEx) → Match (l ∣' r) s → Match (l ∣ r) s
decSound ∅ _ x = dec2 x
decSound ε       ∅ x = dec1 x
decSound ⟦ _ ⟧   ∅ x = dec1 x
decSound (_ ∣ _) ∅ x = dec1 x
decSound (_ ∪ _) ∅ x = dec1 x
decSound (_ *)   ∅ x = dec1 x
decSound ε       ε       x = x
decSound ε       ⟦ _ ⟧   x = x
decSound ε       (_ ∣ _) x = x
decSound ε       (_ ∪ _) x = x
decSound ε       (_ *)   x = x
decSound ⟦ _ ⟧   ε       x = x
decSound ⟦ _ ⟧   ⟦ _ ⟧   x = x
decSound ⟦ _ ⟧   (_ ∣ _) x = x
decSound ⟦ _ ⟧   (_ ∪ _) x = x
decSound ⟦ _ ⟧   (_ *)   x = x
decSound (_ ∣ _) ε       x = x
decSound (_ ∣ _) ⟦ _ ⟧   x = x
decSound (_ ∣ _) (_ ∣ _) x = x
decSound (_ ∣ _) (_ ∪ _) x = x
decSound (_ ∣ _) (_ *)   x = x
decSound (_ ∪ _) ε       x = x
decSound (_ ∪ _) ⟦ _ ⟧   x = x
decSound (_ ∪ _) (_ ∣ _) x = x
decSound (_ ∪ _) (_ ∪ _) x = x
decSound (_ ∪ _) (_ *)   x = x
decSound (_ *)   ε       x = x
decSound (_ *)   ⟦ _ ⟧   x = x
decSound (_ *)   (_ ∣ _) x = x
decSound (_ *)   (_ ∪ _) x = x
decSound (_ *)   (_ *)   x = x

decComp : {s : List Char} → (l r : RegEx) → Match (l ∣ r) s → Match (l ∣' r) s
decComp _ ∅ (dec2 ())
decComp ∅ _ (dec1 ())
decComp ∅ _ (dec2 x) = x
decComp ε       ∅ (dec1 eps)           = eps
decComp (⟦ _ ⟧) ∅ (dec1 char)          = char
decComp (_ ∣ _) ∅ (dec1 (dec1 x))      = dec1 x
decComp (_ ∣ _) ∅ (dec1 (dec2 x))      = dec2 x
decComp (_ ∪ _) ∅ (dec1 (con s x1 x2)) = con s x1 x2
decComp (_ *)   ∅ (dec1 (star x))      = star x
decComp ε       ε       x = x
decComp ε       ⟦ _ ⟧   x = x
decComp ε       (_ ∣ _) x = x
decComp ε       (_ ∪ _) x = x
decComp ε       (_ *)   x = x
decComp ⟦ _ ⟧   ε       x = x
decComp ⟦ _ ⟧   ⟦ _ ⟧   x = x
decComp ⟦ _ ⟧   (_ ∣ _) x = x
decComp ⟦ _ ⟧   (_ ∪ _) x = x
decComp ⟦ _ ⟧   (_ *)   x = x
decComp (_ ∣ _) ε       x = x
decComp (_ ∣ _) ⟦ _ ⟧   x = x
decComp (_ ∣ _) (_ ∣ _) x = x
decComp (_ ∣ _) (_ ∪ _) x = x
decComp (_ ∣ _) (_ *)   x = x
decComp (_ ∪ _) ε       x = x
decComp (_ ∪ _) ⟦ _ ⟧   x = x
decComp (_ ∪ _) (_ ∣ _) x = x
decComp (_ ∪ _) (_ ∪ _) x = x
decComp (_ ∪ _) (_ *)   x = x
decComp (_ *)   ε       x = x
decComp (_ *)   ⟦ _ ⟧   x = x
decComp (_ *)   (_ ∣ _) x = x
decComp (_ *)   (_ ∪ _) x = x
decComp (_ *)   (_ *)   x = x

emptySplit : (s : List Char) → Split s s []
emptySplit   []    = emp
emptySplit (_ ∷ s) = add (emptySplit s)

conrε : {s : List Char}{r : RegEx} → Match r s → Match (r ∪ ε) s
conrε {s} x = con (emptySplit s) x eps

conSound : {s : List Char} → (l r : RegEx) → Match (l ∪' r) s → Match (l ∪ r) s
conSound ∅       _ ()
conSound ε       ∅ ()
conSound ⟦ _ ⟧   ∅ ()
conSound (_ ∣ _) ∅ ()
conSound (_ ∪ _) ∅ ()
conSound (_ *)   ∅ ()
conSound ε ε       x = con emp eps x
conSound ε ⟦ _ ⟧   x = con emp eps x
conSound ε (_ ∣ _) x = con emp eps x
conSound ε (_ ∪ _) x = con emp eps x
conSound ε (_ *)   x = con emp eps x
conSound ⟦ _ ⟧   ε char = con (add emp) char eps
conSound (_ ∣ _) ε x = conrε x
conSound (_ ∪ _) ε x = conrε x
conSound (_ *)   ε x = conrε x
conSound ⟦ _ ⟧   ⟦ _ ⟧   x = x
conSound ⟦ _ ⟧   (_ ∣ _) x = x
conSound ⟦ _ ⟧   (_ ∪ _) x = x
conSound ⟦ _ ⟧   (_ *)   x = x
conSound (_ ∣ _) ⟦ _ ⟧   x = x
conSound (_ ∣ _) (_ ∣ _) x = x
conSound (_ ∣ _) (_ ∪ _) x = x
conSound (_ ∣ _) (_ *)   x = x
conSound (_ ∪ _) ⟦ _ ⟧   x = x
conSound (_ ∪ _) (_ ∣ _) x = x
conSound (_ ∪ _) (_ ∪ _) x = x
conSound (_ ∪ _) (_ *)   x = x
conSound (_ *)   ⟦ _ ⟧   x = x
conSound (_ *)   (_ ∣ _) x = x
conSound (_ *)   (_ ∪ _) x = x
conSound (_ *)   (_ *)   x = x

conεr :{r : RegEx} → {s : List Char} →  Match (ε ∪ r) s → Match r s
conεr (con emp _ x) = x
conεr (con (add _) () _)

splitε : {l1 l2 : List Char} → Split l1 l2 [] → l1 ≡ l2
splitε emp = refl
splitε {a ∷ _}(add x) = cong (_∷_ a) (splitε x)

conrε' : {s : List Char} → {r : RegEx} →  Match (r ∪ ε) s → Match r s
conrε' {[]}       (con (emp {.[]}) x _) = x
conrε' {x ∷ xs}   (con (emp {.(x ∷ xs)}) _ ())
conrε' {.(_ ∷ _)} (con {s2 = []}     (add {l2 = .[]}       x) _ eps)    with splitε x
conrε' {.(_ ∷ l)} (con {s2 = []}     (add {l}{.l} {.[]}    _) x eps) | refl = x
conrε' {.(_ ∷ _)} (con {s2 = x ∷ xs} (add {l2 = .(x ∷ xs)} _) _  ())

conComp : {s : List Char} → (l r : RegEx) → Match (l ∪ r) s → Match (l ∪' r) s
conComp _ ∅       (con _ _ ())
conComp ∅ ε       (con _ () _)
conComp ∅ ⟦ _ ⟧   (con _ () _)
conComp ∅ (_ ∣ _) (con _ () _)
conComp ∅ (_ ∪ _) (con _ () _)
conComp ∅ (_ *)   (con _ () _)
conComp ε ε       x = conεr x
conComp ε ⟦ _ ⟧   x = conεr x
conComp ε (_ ∣ _) x = conεr x
conComp ε (_ ∪ _) x = conεr x
conComp ε (_ *)   x = conεr x
conComp ⟦ _ ⟧   ε x = conrε' x
conComp (_ ∣ _) ε x = conrε' x
conComp (_ ∪ _) ε x = conrε' x
conComp (_ *)   ε x = conrε' x
conComp ⟦ _ ⟧   ⟦ _ ⟧   x = x
conComp ⟦ _ ⟧   (_ ∣ _) x = x
conComp ⟦ _ ⟧   (_ ∪ _) x = x
conComp ⟦ _ ⟧   (_ *)   x = x
conComp (_ ∣ _) ⟦ _ ⟧   x = x
conComp (_ ∣ _) (_ ∣ _) x = x
conComp (_ ∣ _) (_ ∪ _) x = x
conComp (_ ∣ _) (_ *)   x = x
conComp (_ ∪ _) ⟦ _ ⟧   x = x
conComp (_ ∪ _) (_ ∣ _) x = x
conComp (_ ∪ _) (_ ∪ _) x = x
conComp (_ ∪ _) (_ *)   x = x
conComp (_ *)   ⟦ _ ⟧   x = x
conComp (_ *)   (_ ∣ _) x = x
conComp (_ *)   (_ ∪ _) x = x
conComp (_ *)   (_ *)   x = x

starSound : {s : List Char} → (r : RegEx) → Match (r *') s → Match (r *) s
starSound ∅ x = star (dec1 x)
starSound ε x = star (dec1 x)
starSound ⟦ _ ⟧   x = x
starSound (_ ∣ _) x = x
starSound (_ ∪ _) x = x
starSound (_ *)   x = x

starComp : {s : List Char} → (r : RegEx) → Match (r *) s → Match (r *') s
starComp ∅ (star (dec1 eps)) = eps
starComp ∅ (star (dec2 (con _ () _)))
starComp ε (star (dec1 eps)) = eps
starComp ε (star (dec2 (con emp _ x))) = starComp ε x
starComp ε (star (dec2 (con (add _) () _)))
starComp ⟦ _ ⟧   x = x
starComp (_ ∣ _) x = x
starComp (_ ∪ _) x = x
starComp (_ *)   x = x

der : Char → RegEx → RegEx
der x ∅ = ∅
der x ε = ∅
der x ⟦ c ⟧    with x ≟ c
der x ⟦ .x ⟧ | yes refl = ε
der x ⟦ c ⟧  | no ¬p = ∅
der x (l ∣ r) = (der x l) ∣' (der x r)
der x (l ∪ r)   with empty l
der x (l ∪ r) | yes p = ((der x l) ∪' r) ∣' der x r
der x (l ∪ r) | no ¬p = ((der x l) ∪' r)
der x (r *) = (der x r) ∪' (r *)

derSound : {s : List Char} → (r : RegEx) → {x : Char} → Match (der x r) s → Match r (x ∷ s)
derSound ∅ ()
derSound ε ()
derSound         ⟦ c ⟧ {x}  d    with x ≟ c
derSound {[]}    ⟦ x ⟧      _  | yes refl = char
derSound {_ ∷ _} ⟦ c ⟧      () | yes refl
derSound         ⟦ _ ⟧ {_}  ()          | no _
derSound (l ∣ r) {x} d   with decSound (der x l) (der x r) d
derSound (l ∣ r) {x} d | dec1 m = dec1 (derSound l m)
derSound (l ∣ r) {x} d | dec2 m = dec2 (derSound r m)
derSound (l ∪ r)     d   with empty l
derSound (l ∪ r) {x} d | yes p   with decSound (der x l ∪' r) (der x r) d 
derSound (l ∪ r) {x} d | yes p | (dec1 m)   with conSound (der x l) r m
derSound (l ∪ r) {x} d | yes p | (dec1 m) | (con s m1 m2) = con (add s) (derSound l {x} m1) m2
derSound (l ∪ r)     d | yes p | (dec2 m)   with derSound r m
derSound (l ∪ r)     d | yes p | (dec2 m) | l2 = con emp p l2
derSound (l ∪ r) {x} d | no ¬p    with conSound (der x l) r d
derSound (l ∪ r)     d | no ¬p | (con s m1 m2)   with derSound l m1
derSound (l ∪ r)     d | no ¬p | (con s m1 m2) | p = con (add s) p m2
derSound (r *)   {x} d   with conSound (der x r) (r *) d
derSound (r *)   {x} d | con s m1 m2   with derSound r m1
derSound (r *)   {x} d | con s m1 m2 | p = star (dec2 (con (add s) p m2))

void :{A : Set} → ⊥ → A
void = λ ()

eq : {A : Set} → (a : A) → a ≡ a
eq x = refl

derComp : {s : List Char} → (r : RegEx) → {c : Char} → Match r (c ∷ s) → Match (der c r) s
derComp ∅ ()
derComp ε ()
derComp ⟦ x ⟧ char   with x ≟ x
derComp ⟦ x ⟧ char | yes refl = eps
derComp ⟦ x ⟧ char | no ¬p = void (¬p (eq x))
derComp (l ∣ r) {x} (dec1 m) = decComp (der x l) (der x r) (dec1 (derComp l m))
derComp (l ∣ r) {x} (dec2 m) = decComp (der x l) (der x r) (dec2 (derComp r m)) 
derComp (l ∪ r)      m                    with empty l
derComp (l ∪ r) {x} (con emp m1 m2)     | yes p = decComp (der x l ∪' r) (der x r) (dec2 (derComp r m2))
derComp (l ∪ r) {x} (con (add s) m1 m2) | yes p = decComp (der x l ∪' r) (der x r) (dec1 (conComp (der x l) r (con s (derComp l m1) m2)))
derComp (l ∪ r)     (con emp m1 m2)     | no ¬p = void (¬p m1)
derComp (l ∪ r) {x} (con (add s) m1 m2) | no ¬p = conComp (der x l) r (con s (derComp l m1) m2)
derComp (r *)       (star (dec1 ()))
derComp (r *)       (star (dec2 (con emp m1 m2)))     = derComp (r *) m2
derComp (r *)   {x} (star (dec2 (con (add s) m1 m2))) = conComp (der x r) (r *) (con s (derComp r m1) m2)

-- not based on the paper

parse : (r : RegEx) → (s : List Char) → Dec (Match r s)
parse r []   with empty r
parse r [] | yes p = yes p
parse r [] | no ¬p = no ¬p
parse r (x ∷ xs)   with parse (der x r) xs
parse r (x ∷ xs) | yes p = yes (derSound r p)
parse r (x ∷ xs) | no ¬p = no (λ m → ¬p (derComp r m))

data PreMatch (r : RegEx) (s : List Char): Set where
 pm : {t : List Char} → Match r (s ++ t) → PreMatch r s

red : RegEx → RegEx
red ∅       = ∅
red ε       = ε
red ⟦ x ⟧   = ⟦ x ⟧
red (l ∣ r) = l ∣' r
red (l ∪ r) = l ∪' r
red (r *)   = r *'

redSound : {s : List Char} → (r : RegEx) → Match (red r) s → Match r s
redSound ∅       m = m
redSound ε       m = m
redSound ⟦ c ⟧   m = m
redSound (l ∣ r) m = decSound l r m
redSound (l ∪ r) m = conSound l r m
redSound (r *)   m = starSound r m

redComp : {s : List Char} → (r : RegEx) → Match r s → Match (red r) s
redComp ∅       m = m
redComp ε       m = m
redComp ⟦ c ⟧   m = m
redComp (l ∣ r) m = decComp l r m
redComp (l ∪ r) m = conComp l r m
redComp (r *)   m = starComp r m

unSplit : (t1 t2 : List Char) → Split (t1 ++ t2) t1 t2
unSplit [] t2 = emp
unSplit (x ∷ t1) t2 = add (unSplit t1 t2)

preParse : (r : RegEx) → (s : List Char) → Dec (PreMatch r s)
preParse ∅ [] = no (λ { (pm ())})
preParse ε [] = yes (pm eps)
preParse ⟦ c ⟧ [] = yes (pm char)
preParse (l ∣ r) [] with preParse l [] | preParse r []
preParse (l ∣ r) [] | yes (pm m) | _ = yes (pm (dec1 m))
preParse (l ∣ r) [] | no _ | yes (pm m) = yes (pm (dec2 m))
preParse (l ∣ r) [] | no ¬p1 | no ¬p2 = no (λ { (pm (dec1 x)) → ¬p1 (pm x) ; (pm (dec2 x)) → ¬p2 (pm x)})
preParse (l ∪ r) [] with preParse l [] | preParse r []
preParse (l ∪ r) [] | yes (pm {t1} m1) | yes (pm {t2} m2) = yes (pm (con (unSplit t1 t2) m1 m2))
preParse (l ∪ r) [] | yes p | (no ¬p) = no (λ { (pm (con _ _  m)) → ¬p (pm m)})
preParse (l ∪ r) [] | no ¬p | p2 = no (λ { (pm (con _ m _)) → ¬p (pm m)})
preParse (r *) [] = yes (pm (star (dec1 eps)))
preParse ∅ (x ∷ xs) = no (λ { (pm ())})
preParse ε (x ∷ xs) = no (λ { (pm ())})
preParse ⟦ c ⟧ (x ∷ []) with x ≟ c
preParse ⟦ c ⟧ (.c ∷ []) | yes refl = yes (pm char)
preParse ⟦ c ⟧ (x ∷ []) | no ¬p = no (λ { (pm char) → ¬p refl})
preParse ⟦ c ⟧ (x1 ∷ x2 ∷ xs) = no (λ { (pm ())})
preParse (l ∣ r) (x ∷ xs) with preParse (der x l) xs | preParse (der x r) xs
preParse (l ∣ r) (x ∷ xs) | yes (pm m) | _ = yes (pm (dec1 (derSound l m)))
preParse (l ∣ r) (x ∷ xs) | no ¬p | yes (pm m) = yes (pm (dec2 (derSound r m)))
preParse (l ∣ r) (x ∷ xs) | no ¬p1 | no ¬p2 = no (λ { (pm (dec1 m)) → ¬p1 (pm (derComp l m)) ; (pm (dec2 m)) → ¬p2 (pm (derComp r m))})
preParse (l ∪ r) (x ∷ xs) with preParse (der x (l ∪ r)) xs
preParse (l ∪ r) (x ∷ xs) | yes (pm m) = yes (pm (derSound (l ∪ r) m))
preParse (l ∪ r) (x ∷ xs) | no ¬p = no (λ { (pm m) → ¬p (pm (derComp (l ∪ r) m))})
preParse (r *) (x ∷ xs) with preParse (der x (r *)) xs
preParse (r *) (x ∷ xs) | yes (pm m) = yes (pm (derSound (r *) m))
preParse (r *) (x ∷ xs) | no ¬p = no (λ { (pm m) → ¬p (pm (derComp (r *) m))}) 

--ppAccept : {r : RegEx} → {s : List Char} → PreMatch r s → Dec (Match r s)
--ppAccept {r} {[]} (pm x) = empty r
--ppAccept {r} {x ∷ s} (pm x₁) = {!!}

ders : List Char → RegEx → RegEx
ders [] r = r
ders (x ∷ s) r = ders s (der x r)

dersSound : (r : RegEx) → (s : List Char) → Match (ders s r) [] → Match r s
dersSound ∅ [] ()
dersSound ∅ (x ∷ s) x₁ = derSound ∅ (dersSound ∅ s x₁)
dersSound ε [] x = x
dersSound ε (x ∷ s) x₁ = {!!}
dersSound ⟦ x ⟧ s x₁ = {!!}
dersSound (r ∣ r₁) s x = {!!}
dersSound (r ∪ r₁) s x = {!!}
dersSound (r *) s x = {!!}

dersComp : (r : RegEx) → (s : List Char) → Match r s → Match (ders s r) [] 
dersComp ∅ s ()
dersComp ε [] x = x
dersComp ε (x ∷ s) ()
dersComp ⟦ c ⟧ [] ()
dersComp ⟦ c ⟧ (x ∷ []) m with x ≟ c
dersComp ⟦ c ⟧ (.c ∷ []) m | yes refl = eps
dersComp ⟦ c ⟧ (.c ∷ []) char | no ¬p = void (¬p refl)
dersComp ⟦ c ⟧ (x1 ∷ x2 ∷ s) ()
dersComp (l ∣ r) [] x = x
dersComp (l ∣ r) (x ∷ s) m = dersComp (der x l ∣' der x r) s (derComp (l ∣ r) m)
dersComp (l ∪ r) [] x = x
dersComp (l ∪ r) (x ∷ s) m with empty l
dersComp (l ∪ r) (x ∷ s) (con emp m m₁) | yes p = dersComp ((der x l ∪' r) ∣' der x r) s (derComp ((ε ∣ l) ∪ r) (con emp (dec2 m) m₁))
dersComp (l ∪ r) (x ∷ s) (con (add x₁) m m₁) | yes p = dersComp ((der x l ∪' r) ∣' der x r) s (derComp ((ε ∣ l) ∪ r) (con (add x₁) (dec2 m) m₁))
dersComp (l ∪ r) (x ∷ s) (con emp m m₁) | no ¬p = void (¬p m)
dersComp (l ∪ r) (x ∷ s) (con (add x₁) m m₁) | no ¬p = dersComp (der x l ∪' r) s (conComp (der x l) r (con x₁ (derComp l m) m₁))
dersComp (r *) [] x = x
dersComp (r *) (x ∷ s) m = dersComp (der x r ∪' (r *)) s (derComp (r *) m)

--Usefull stuf??

Token : Set → Set
Token A = RegEx × (List Char → A)

lex : {A : Set} → List Char → List (Token A) → Maybe A
lex {A} s [] = nothing
lex {A} s (x ∷ rs) = {!!}
