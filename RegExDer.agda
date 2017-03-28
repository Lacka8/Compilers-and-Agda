module RegExDer where

--http://homepages.dcc.ufmg.br/~camarao/certified-parsing-regex.pdf

open import Data.Char using(Char;_≟_)
open import Data.List using(List;[];_∷_;[_];_++_)
open import Relation.Binary.PropositionalEquality using(_≡_;refl)
open import Relation.Nullary using(Dec;yes;no;¬_)
open import Data.Sum using(_⊎_) renaming(inj₁ to inj1;inj₂ to inj2)
open import Data.Empty using(⊥)

data RegEx : Set where
 ∅    : RegEx
 ε    : RegEx
 ⟦_⟧  : Char  → RegEx
 _∣_  : RegEx → RegEx → RegEx
 _⊹_ : RegEx → RegEx → RegEx
 _*   : RegEx → RegEx

data Split {A : Set}: List A → List A → List A → Set where
 emp : {l : List A} → Split l [] l
 add : {l l1 l2 : List A}{a : A} → Split l l1 l2 → Split (a ∷ l) (a ∷ l1) l2

data Match : RegEx → List Char → Set where
 eps  : Match ε []
 char : {c : Char} → Match ⟦ c ⟧ [ c ]
 dec1 : {r1 r2 : RegEx}{s : List Char} → Match r1 s → Match (r1 ∣ r2) s 
 dec2 : {r1 r2 : RegEx}{s : List Char} → Match r2 s → Match (r1 ∣ r2) s 
 con  : {r1 r2 : RegEx}{s s1 s2 : List Char} → Split s s1 s2 → Match r1 s1 → Match  r2 s2 → Match (r1 ⊹ r2) s
 star : {r : RegEx}{s : List Char} → Match (ε ∣ (r ⊹ (r *))) s → Match (r *) s

empty∣ :{r1 r2 : RegEx} → ¬ Match r1 [] → ¬ Match r2 [] → ¬ Match (r1 ∣ r2) []
empty∣ p1 p2 (dec1 x2) = p1 x2
empty∣ p1 p2 (dec2 x2) = p2 x2

empty⊹1 :{r1 r2 : RegEx} → ¬ Match r1 [] →  ¬ Match (r1 ⊹ r2) [] 
empty⊹1 p (con emp m1 m2) = p m1

empty⊹2 :{r1 r2 : RegEx} → ¬ Match r2 [] →  ¬ Match (r1 ⊹ r2) [] 
empty⊹2 p (con emp m1 m2) = p m2

empty : (r : RegEx) → Dec (Match r [])
empty ∅ = no (λ ())
empty ε = yes eps
empty ⟦ c ⟧ = no (λ ())
empty (r1 ∣ r2) with empty r1 | empty r2
empty (r1 ∣ r2) | yes p | p2 = yes (dec1 p)
empty (r1 ∣ r2) | no ¬p | (yes p) = yes (dec2 p)
empty (r1 ∣ r2) | no ¬p | (no ¬p1) = no (empty∣ ¬p ¬p1)
empty (r1 ⊹ r2) with empty r1 | empty r2
empty (r1 ⊹ r2) | yes p1 | yes p2 = yes (con emp p1 p2)
empty (r1 ⊹ r2) | yes p1 | no ¬p2 = no (empty⊹2 ¬p2)
empty (r1 ⊹ r2) | no ¬p1 | p2 = no (empty⊹1 ¬p1)
empty (r *) = yes (star (dec1 eps))

_∣'_ : RegEx → RegEx → RegEx
∅ ∣' r = r
r ∣' ∅ = r
r1 ∣' r2 = r1 ∣ r2

_⊹'_ : RegEx → RegEx → RegEx
∅ ⊹' _ = ∅
_ ⊹' ∅ = ∅
ε ⊹' r = r
r ⊹' ε = r
r1 ⊹' r2 = r1 ⊹ r2

_*' : RegEx → RegEx
∅ *' = ε
ε *' = ε
r *' = r *

lemma1 : {s : List Char} → (r1 r2 : RegEx) → Match (r1 ∣' r2) s → Match (r1 ∣ r2) s
lemma1 ∅ _ x = dec2 x
lemma1 ε ∅ x = dec1 x
lemma1 ⟦ _ ⟧ ∅ x = dec1 x
lemma1 (_ ∣ _) ∅ x = dec1 x
lemma1 (_ ⊹ _) ∅ x = dec1 x
lemma1 (_ *) ∅ x = dec1 x
lemma1 ε ε x = x
lemma1 ε ⟦ _ ⟧ x₁ = x₁
lemma1 ε (_ ∣ _) x = x
lemma1 ε (_ ⊹ _) x = x
lemma1 ε (_ *) x = x
lemma1 ⟦ _ ⟧ ε x = x
lemma1 ⟦ _ ⟧ ⟦ _ ⟧ x = x
lemma1 ⟦ _ ⟧ (_ ∣ _) x = x
lemma1 ⟦ _ ⟧ (_ ⊹ _) x = x
lemma1 ⟦ _ ⟧ (_ *) x = x
lemma1 (_ ∣ _) ε x = x
lemma1 (_ ∣ _) ⟦ _ ⟧ x = x
lemma1 (_ ∣ _) (_ ∣ _) x = x
lemma1 (_ ∣ _) (_ ⊹ _) x = x
lemma1 (_ ∣ _) (_ *) x = x
lemma1 (_ ⊹ _) ε x = x
lemma1 (_ ⊹ _) ⟦ _ ⟧ x = x
lemma1 (_ ⊹ r2) (r3 ∣ r4) x = x
lemma1 (_ ⊹ r2) (r3 ⊹ r4) x = x
lemma1 (_ ⊹ r2) (r3 *) x = x
lemma1 (_ *) ε x = x
lemma1 (_ *) ⟦ _ ⟧ x = x
lemma1 (_ *) (_ ∣ _) x = x
lemma1 (_ *) (_ ⊹ _) x = x
lemma1 (_ *) (_ *) x = x

lemma2 : {s : List Char} → (r1 r2 : RegEx) → Match (r1 ∣ r2) s → Match (r1 ∣' r2) s
lemma2 ∅ r2 (dec1 ())
lemma2 ∅ r2 (dec2 x) = x
lemma2 .ε ∅ (dec1 eps) = eps
lemma2 .(⟦ _ ⟧) ∅ (dec1 char) = char
lemma2 .(_ ∣ _) ∅ (dec1 (dec1 x)) = dec1 x
lemma2 .(_ ∣ _) ∅ (dec1 (dec2 x)) = dec2 x
lemma2 .(_ ⊹ _) ∅ (dec1 (con x x₁ x₂)) = con x x₁ x₂
lemma2 .(_ *) ∅ (dec1 (star x)) = star x
lemma2 r1 ∅ (dec2 ())
lemma2 ε ε x = x
lemma2 ε ⟦ x ⟧ x₁ = x₁
lemma2 ε (r2 ∣ r3) x = x
lemma2 ε (r2 ⊹ r3) x = x
lemma2 ε (r2 *) x = x
lemma2 ⟦ x ⟧ ε x₁ = x₁
lemma2 ⟦ x ⟧ ⟦ x₁ ⟧ x₂ = x₂
lemma2 ⟦ x ⟧ (r2 ∣ r3) x₁ = x₁
lemma2 ⟦ x ⟧ (r2 ⊹ r3) x₁ = x₁
lemma2 ⟦ x ⟧ (r2 *) x₁ = x₁
lemma2 (r1 ∣ r2) ε x = x
lemma2 (r1 ∣ r2) ⟦ x ⟧ x₁ = x₁
lemma2 (r1 ∣ r2) (r3 ∣ r4) x = x
lemma2 (r1 ∣ r2) (r3 ⊹ r4) x = x
lemma2 (r1 ∣ r2) (r3 *) x = x
lemma2 (r1 ⊹ r2) ε x = x
lemma2 (r1 ⊹ r2) ⟦ x ⟧ x₁ = x₁
lemma2 (r1 ⊹ r2) (r3 ∣ r4) x = x
lemma2 (r1 ⊹ r2) (r3 ⊹ r4) x = x
lemma2 (r1 ⊹ r2) (r3 *) x = x
lemma2 (r1 *) ε x = x
lemma2 (r1 *) ⟦ x ⟧ x₁ = x₁
lemma2 (r1 *) (r2 ∣ r3) x = x
lemma2 (r1 *) (r2 ⊹ r3) x = x
lemma2 (r1 *) (r2 *) x = x

emptySplit : (s : List Char) → Split s s []
emptySplit [] = emp
emptySplit (x ∷ s) = add (emptySplit s)

conε : {s : List Char}{r : RegEx} → Match r s → Match (r ⊹ ε) s
conε {s} x = con (emptySplit s) x eps



lemma3 : {s : List Char} → (r1 r2 : RegEx) → Match (r1 ⊹' r2) s → Match (r1 ⊹ r2) s
lemma3 ∅ r2 ()
lemma3 ε ∅ ()
lemma3 ⟦ x ⟧ ∅ ()
lemma3 (r1 ∣ r2) ∅ ()
lemma3 (r1 ⊹ r2) ∅ ()
lemma3 (r1 *) ∅ ()
lemma3 ε ε x = con emp eps x
lemma3 ε ⟦ x ⟧ x₁ = con emp eps x₁
lemma3 ε (r2 ∣ r3) x = con emp eps x
lemma3 ε (r2 ⊹ r3) x = con emp eps x
lemma3 ε (r2 *) x = con emp eps x
lemma3 ⟦ x ⟧ ε char = con (add emp) char eps
lemma3 ⟦ _ ⟧ ⟦ _ ⟧ x = x
lemma3 ⟦ x ⟧ (r2 ∣ r3) x₁ = x₁
lemma3 ⟦ x ⟧ (r2 ⊹ r3) x₁ = x₁
lemma3 ⟦ x ⟧ (r2 *) x₁ = x₁
lemma3 (r1 ∣ r2) ε x = conε x
lemma3 (r1 ∣ r2) ⟦ x ⟧ x₁ = x₁
lemma3 (r1 ∣ r2) (r3 ∣ r4) x = x
lemma3 (r1 ∣ r2) (r3 ⊹ r4) x = x
lemma3 (r1 ∣ r2) (r3 *) x = x
lemma3 (r1 ⊹ r2) ε x = conε x
lemma3 (r1 ⊹ r2) ⟦ x ⟧ x₁ = x₁
lemma3 (r1 ⊹ r2) (r3 ∣ r4) x = x
lemma3 (r1 ⊹ r2) (r3 ⊹ r4) x = x
lemma3 (r1 ⊹ r2) (r3 *) x = x
lemma3 (r1 *) ε x = conε x
lemma3 (r1 *) ⟦ x ⟧ x₁ = x₁
lemma3 (r1 *) (r2 ∣ r3) x = x
lemma3 (r1 *) (r2 ⊹ r3) x = x
lemma3 (r1 *) (r2 *) x = x

conε2 :{r : RegEx} → {s : List Char} →  Match (ε ⊹ r) s → Match r s
conε2 (con emp x₁ x₂) = x₂
conε2 (con (add x) () x₂)

cong : {A B : Set}{a1 a2 : A} → (f : A → B) → a1 ≡ a2 → f a1 ≡ f a2
cong f refl = refl

splitε : {l1 l2 : List Char} → Split l1 l2 [] → l1 ≡ l2
splitε {l1} emp = refl
splitε {l1 = (a ∷ as)}(add x) = cong (_∷_ a) (splitε x)

conε3 : {r : RegEx} → {s : List Char} →  Match (r ⊹ ε) s → Match r s
conε3 {r} {[]} (con (emp {.[]}) x₁ x₂) = x₁
conε3 {r} {x ∷ s} (con (emp {.(x ∷ s)}) x₁ ())
conε3 {r} {.(_ ∷ _)} (con {s2 = []} (add {l} {l1} {l2 = .[]} x) x₁ eps) with splitε x
conε3 {r} {.(_ ∷ l)} (con {_} {_} {_} {_} {[]} (add {l} {.l} {.[]} x) x₁ eps) | refl = x₁
conε3 {r} {.(_ ∷ _)} (con {s2 = x ∷ s2} (add {l2 = .(x ∷ s2)} x₁) x₂ ())

lemma4 : {s : List Char} → (r1 r2 : RegEx) → Match (r1 ⊹ r2) s → Match (r1 ⊹' r2) s
lemma4 _ ∅ (con _ _ ())
lemma4 ∅ ε (con x () x₂)
lemma4 ∅ ⟦ x ⟧ (con x₁ () x₃)
lemma4 ∅ (r2 ∣ r3) (con x () x₂)
lemma4 ∅ (r2 ⊹ r3) (con x () x₂)
lemma4 ∅ (r2 *) (con x () x₂)
lemma4 ε ε x = conε2 x
lemma4 ε ⟦ x ⟧ x₁ = conε2 x₁
lemma4 ε (r2 ∣ r3) x = conε2 x
lemma4 ε (r2 ⊹ r3) x = conε2 x
lemma4 ε (r2 *) x = conε2 x
lemma4 {s} ⟦ x ⟧ ε x₁ = conε3 x₁
lemma4 ⟦ x ⟧ ⟦ x₁ ⟧ x₂ = x₂
lemma4 ⟦ x ⟧ (r2 ∣ r3) x₁ = x₁
lemma4 ⟦ x ⟧ (r2 ⊹ r3) x₁ = x₁
lemma4 ⟦ x ⟧ (r2 *) x₁ = x₁
lemma4 {s} (r1 ∣ r2) ε x = conε3 x
lemma4 (r1 ∣ r2) ⟦ x ⟧ x₁ = x₁
lemma4 (r1 ∣ r2) (r3 ∣ r4) x = x
lemma4 (r1 ∣ r2) (r3 ⊹ r4) x = x
lemma4 (r1 ∣ r2) (r3 *) x = x
lemma4 {s} (r1 ⊹ r2) ε x = conε3 x
lemma4 (r1 ⊹ r2) ⟦ x ⟧ x₁ = x₁
lemma4 (r1 ⊹ r2) (r3 ∣ r4) x = x
lemma4 (r1 ⊹ r2) (r3 ⊹ r4) x = x
lemma4 (r1 ⊹ r2) (r3 *) x = x
lemma4 {s} (r1 *) ε x = conε3 x
lemma4 (r1 *) ⟦ x ⟧ x₁ = x₁
lemma4 (r1 *) (r2 ∣ r3) x = x
lemma4 (r1 *) (r2 ⊹ r3) x = x
lemma4 (r1 *) (r2 *) x = x

lemma5 : {s : List Char} → (r : RegEx) → Match (r *') s → Match (r *) s
lemma5 ∅ x = star (dec1 x)
lemma5 ε x = star (dec1 x)
lemma5 ⟦ x ⟧ x₁ = x₁
lemma5 (r ∣ r₁) x = x
lemma5 (r ⊹ r₁) x = x
lemma5 (r *) x = x

lemma6 : {s : List Char} → (r : RegEx) → Match (r *) s → Match (r *') s
lemma6 ∅ (star (dec1 eps)) = eps
lemma6 ∅ (star (dec2 (con x () x₂)))
lemma6 ε (star (dec1 eps)) = eps
lemma6 ε (star (dec2 (con emp x₁ x₂))) = lemma6 ε x₂
lemma6 ε (star (dec2 (con (add x) () x₂)))
lemma6 ⟦ x ⟧ x₁ = x₁
lemma6 (r ∣ r₁) x = x
lemma6 (r ⊹ r₁) x = x
lemma6 (r *) x = x

der : Char → RegEx → RegEx
der x ∅ = ∅
der x ε = ∅
der x ⟦ x₁ ⟧ with x ≟ x₁
der x ⟦ .x ⟧ | yes refl = ε
der x ⟦ x₁ ⟧ | no ¬p = ∅
der x (x₁ ∣ x₂) = (der x x₁) ∣' (der x x₂)
der x (x₁ ⊹ x₂) with empty x₁
der x (x₁ ⊹ x₂) | yes p = ((der x x₁) ⊹' x₂) ∣' der x x₂
der x (x₁ ⊹ x₂) | no ¬p = ((der x x₁) ⊹' x₂)
der x (x₁ *) = (der x x₁) ⊹' (x₁ *)

-- abab

therome1 : (r : RegEx) → {s : List Char} → {c : Char} → Match (der c r) s → Match r (c ∷ s)
therome1 ∅ ()
therome1 ε ()
therome1 ⟦ x ⟧ {s} {c} x₁ with c ≟ x
therome1 ⟦ x ⟧ {[]} {.x} x₁ | yes refl = char
therome1 ⟦ x ⟧ {x₁ ∷ s} {.x} () | yes refl
therome1 ⟦ x ⟧ {s} {c} () | no ¬p
therome1 (r ∣ r₁){s} {c} x with lemma1 (der c r) (der c r₁) x
therome1 (r ∣ r₁) {s} {c} x | dec1 l = dec1 (therome1 r l)
therome1 (r ∣ r₁) {s} {c} x | dec2 l = dec2 (therome1 r₁ l)
therome1 (r ⊹ r₁) x with empty r
therome1 (r ⊹ r₁) {s} {c} x | yes p with lemma1 (der c r ⊹' r₁) (der c r₁) x 
therome1 (r ⊹ r₁) {s} {c} x | yes p | (dec1 l) with lemma3 (der c r) r₁ l
therome1 (r ⊹ r₁) {s} {c} x₁ | yes p | (dec1 l) | (con x l2 l3) = con (add x) (therome1 r {c = c} l2) l3
therome1 (r ⊹ r₁) x | yes p | (dec2 l) with therome1 r₁ l
...| l2 = con emp p l2
therome1 (r ⊹ r₁) {s} {c} x | no ¬p with lemma3 (der c r) r₁ x
therome1 (r ⊹ r₁) x | no ¬p | (con x₁ l l₁) with therome1 r l
...| t = con (add x₁) t l₁
therome1 (r *) {s} {c} x with lemma3 (der c r) (r *) x
therome1 (r *) {s} {c} x | con x₁ l l₁ with therome1 r l
...| t = star (dec2 (con (add x₁) t l₁))

match∅ : ¬ Match ∅ []
match∅ = λ ()

void :{A : Set} → ⊥ → A
void = λ ()

eq : {A : Set} → (a : A) → a ≡ a
eq x = refl

therome2 : (r : RegEx) → {s : List Char} → {c : Char} → Match r (c ∷ s) → Match (der c r) s
therome2 ∅ ()
therome2 ε ()
therome2 ⟦ x ⟧ {s} {.x} char with x ≟ x
therome2 ⟦ x ⟧ {.[]} {.x} char | yes refl = eps
therome2 ⟦ x ⟧ {.[]} {.x} char | no ¬p = void (¬p (eq x))
therome2 (r ∣ r₁) {s} {c} (dec1 x) = lemma2 (der c r) (der c r₁) (dec1 (therome2 r x))
therome2 (r ∣ r₁) {s} {c} (dec2 x) = lemma2 (der c r) (der c r₁) (dec2 (therome2 r₁ x)) 
therome2 (r ⊹ r₁) x with empty r
therome2 (r ⊹ r₁) {l} {c}(con emp x₁ x₂) | yes p = lemma2  ((der c r) ⊹' r₁) (der c r₁) (dec2 (therome2 r₁ x₂))
therome2 (r ⊹ r₁){l} {c}(con (add x) x₁ x₂) | yes p = lemma2 (der c r  ⊹' r₁) (der c  r₁) (dec1 (lemma4 (der c r) r₁ (con x (therome2 r x₁) x₂)))
therome2 (r ⊹ r₁) (con emp x₁ x₂) | no ¬p = void (¬p x₁)
therome2 (r ⊹ r₁){l} {c} (con (add x) x₁ x₂) | no ¬p = lemma4 (der c r) r₁ (con x (therome2 r x₁) x₂)
therome2 (r *) (star (dec1 ()))
therome2 (r *) (star (dec2 (con emp x₁ x₂))) = therome2 (r *) x₂
therome2 (r *){l} {c}(star (dec2 (con (add x) x₁ x₂))) = lemma4 (der c r) (r *) (con x (therome2 r x₁) x₂)



