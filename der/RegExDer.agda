module RegExDer where

--http://homepages.dcc.ufmg.br/~camarao/certified-parsing-regex.pdf

open import Data.Char using(Char)
open import Data.Char.Unsafe using(_≟_)
open import Data.List using(List;[];_∷_;[_];_++_;length;take;foldr)
open import Relation.Binary.PropositionalEquality using(_≡_;refl;cong;trans)
open import Relation.Nullary using(Dec;yes;no;¬_)
open import Data.Sum using(_⊎_) renaming(inj₁ to inj1;inj₂ to inj2)
open import Data.Empty using(⊥) renaming(⊥-elim to void)
open import Data.String using(toList)
open import Data.Product using(_×_;Σ;_,_) renaming(proj₁ to proj1;proj₂ to proj2)
open import Data.Nat using (ℕ;suc;zero;_≤_;z≤n;s≤s)
open import Data.Maybe using(Maybe;just;nothing)

open import RegEx
open import Match
open import Empty
open import SmartCons (_≟_) 
open import Der (_≟_)
open import Matches (_≟_)

open import IO


main = run (putStr  "Hello \n")

-- -- next?

-- ders : List Char → RegEx Char → RegEx Char
-- ders s r = foldr der r s

-- dersSound : {s1 s2 : List Char} → (r : RegEx Char) → Match (ders s1 r) s2 → Match r (s1 ++ s2)
-- dersSound r m = {!!}

-- -- try???

-- accept : (s : List Char) → (r : RegEx Char) → Dec (Match r s)
-- accept [] r = empty r
-- accept (x ∷ s) r with accept s (der x r)
-- accept (x ∷ s) r | yes p = {!!}
-- accept (x ∷ s) r | no ¬p = {!!}

-- --longest match



-- --parser?

-- data PreMatch {A : Set} {r : RegEx A}{s1 : List A} (m : Match r s1)(s : List A) : Set where
--  pre : {s2 : List A} → Split s s1 s2 → PreMatch m s


-- data _≤L_ {A : Set}: List A → List A → Set where
--  emp : {as : List A} → []  ≤L as 
--  step : {as bs : List A} {a b : A} → as ≤L bs → (a ∷ as) ≤L (b ∷ bs)


-- data LongerPreMatch {A : Set}{r1 r2 : RegEx A}{s1 s1' : List A} (s : List A){ m1 : Match r1 s1}{m2 : Match r2 s1'}: PreMatch m1 s → PreMatch m2 s → Set where
--  longer : {p1 : PreMatch m1 s}{p2 : PreMatch m2 s} →  s1 ≤L s1' → LongerPreMatch s p1 p2


-- data LongPreMatch {A : Set}{r : RegEx A}{s1 : List A} (s : List A){ m1 : Match r s1} (p1 : PreMatch m1 s): Set where 
--   this : {s1' : List A}{m2 : Match r s1'}{p2 : PreMatch m2 s} → LongerPreMatch s p2 p1 → LongPreMatch s p1


-- open import Data.Maybe


-- data Token {A B : Set} : Set where
--  token : RegEx A → (List A → B) → Token {A} {B} 

-- Tokens : {A B : Set} → Set
-- Tokens {A} {B} = List (Token {A} {B})

-- tokenParser : List Char → RegEx Char → Maybe(List Char × List Char)
-- tokenParser s r = tp s [] nothing r
--   where
--   tp :  List Char → List Char → Maybe (List Char × List Char) → RegEx Char → Maybe (List Char × List Char)
--   tp [] _ b r = b
--   tp (x ∷ xs) h b r with der x r
--   ...| d with empty d
--   tp (x ∷ xs) h b r | d | yes p = tp xs (x ∷ h) (just (x ∷ h , xs)) d
--   tp (x ∷ xs) h b r | d | no ¬p = tp xs (x ∷ h) b d

-- parse : List Char → Tokens{Char}{ℕ} → List ℕ
-- parse s x = parseCore s [] nothing x
--   where
--   parseCore : List Char → List Char → Maybe ℕ → Tokens{Char}{ℕ} → List ℕ
--   parseCore [] r (just b) t = [ b ]
--   parseCore [] r nothing t = []
--   parseCore (x ∷ xs) r  b t = {!!}

-- --TESTS


-- parse' : (r : RegEx Char) → (s : List Char) → Dec (Match r s)
-- parse' r []   with empty r
-- parse' r [] | yes p = yes p
-- parse' r [] | no ¬p = no ¬p
-- parse' r (x ∷ xs)   with parse' (der x r) xs
-- parse' r (x ∷ xs) | yes p = yes (derSound r p)
-- parse' r (x ∷ xs) | no ¬p = no (λ m → ¬p (derComp r m))

-- r1 : RegEx Char
-- r1 = ⟦ 'a' ⟧ ∣ ⟦ 'b' ⟧

-- p1 = parse' r1 (toList "c")
