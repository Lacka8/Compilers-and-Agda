open import Relation.Binary using(Decidable)
open import Relation.Binary.PropositionalEquality using(_≡_)

module Matches {A : Set} (_≟_ : Decidable {A = A} _≡_) where

open import Data.List
open import Relation.Nullary using(Dec;yes;no;¬_)
open import Data.Empty using(⊥) renaming (⊥-elim to void)


open import RegEx
open import Match
open import Empty
open import SmartCons (_≟_) 
open import Der (_≟_)

noMatch :{r : RegEx A}{x : A}{xs : List A} →  ¬ Match (der x r) xs → ¬ Match r (x ∷ xs)
noMatch {r} ¬p m = ¬p (derComp r m)

matchDec : (r : RegEx A) → (l : List A) → Dec (Match r l)
matchDec r [] with empty r
matchDec r [] | yes p = yes p
matchDec r [] | no ¬p = no ¬p
matchDec r (x ∷ xs) with matchDec (der x r) xs
matchDec r (x ∷ xs) | yes p = yes (derSound r p)
matchDec r (x ∷ xs) | no ¬p = no (noMatch ¬p)

data PrefixMatch  {A : Set} (r : RegEx A) (l : List A) : Set where 
  pre : {s1 s2 : List A} → Split l s1 s2 → Match r s1 → PrefixMatch r l

noEmptyPrefixMatch :{r : RegEx A} → ¬ Match r [] → ¬ PrefixMatch r []
noEmptyPrefixMatch ¬p (pre emp m) = ¬p m

noPrefixMatch : {r : RegEx A}{x : A}{xs : List A} → ¬ Match r [] → ¬ (PrefixMatch (der x r) xs) → ¬ (PrefixMatch r (x ∷ xs))
noPrefixMatch ¬p1 ¬p2 (pre emp m) = ¬p1 m
noPrefixMatch {r} ¬p1 ¬p2 (pre (add s) m) = ¬p2 (pre s (derComp r m))

prefixMatchDec : (r : RegEx A) → (l : List A) → Dec (PrefixMatch r l)
prefixMatchDec r [] with empty r
prefixMatchDec r [] | yes p = yes (pre emp p)
prefixMatchDec r [] | no ¬p = no (noEmptyPrefixMatch ¬p)
prefixMatchDec r (x ∷ xs)  with empty r
prefixMatchDec r (x ∷ xs) | yes p = yes (pre emp p)
prefixMatchDec r (x ∷ xs) | no ¬p with prefixMatchDec (der x r) xs
prefixMatchDec r (x ∷ xs) | no ¬p | yes (pre s m) = yes (pre (add s) (derSound r m))
prefixMatchDec r (x ∷ xs) | no ¬p | no ¬p' = no (noPrefixMatch ¬p ¬p')

data SubstringMatch {A : Set}(r : RegEx A)(l : List A) : Set where
  sub : {s1 s2 : List A} → Split l s1 s2 → PrefixMatch r s2 → SubstringMatch r l

noEmptySubstringMatch :{r : RegEx A} → ¬ Match r [] → ¬ SubstringMatch r []
noEmptySubstringMatch ¬p (sub emp (pre emp m)) = ¬p m

noSubstringMatch : {r : RegEx A} {x : A}{xs : List A}→ ¬ PrefixMatch r (x ∷ xs) → ¬ SubstringMatch r xs → ¬ SubstringMatch r (x ∷ xs)
noSubstringMatch ¬p1 ¬p2 (sub emp (pre s2 m)) = ¬p1 (pre s2 m)
noSubstringMatch ¬p1 ¬p2 (sub (add s1) (pre s2 m)) =  ¬p2 (sub s1 (pre s2 m))

substringMatchDec : (r : RegEx A) → (l : List A) → Dec (SubstringMatch r l)
substringMatchDec r [] with empty r
substringMatchDec r [] | yes p = yes (sub emp (pre emp p))
substringMatchDec r [] | no ¬p = no (noEmptySubstringMatch ¬p)
substringMatchDec r (x ∷ xs) with prefixMatchDec r (x ∷ xs)
substringMatchDec r (x ∷ xs) | yes (pre s m) = yes (sub emp (pre s m))
substringMatchDec r (x ∷ xs) | no ¬p with substringMatchDec r xs
substringMatchDec r (x ∷ xs) | no ¬p | yes (sub s1 (pre s2 m)) = yes (sub (add s1) (pre s2 m)) 
substringMatchDec r (x ∷ xs) | no ¬p | no ¬p' = no (noSubstringMatch ¬p ¬p')
