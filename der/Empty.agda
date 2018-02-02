module Empty where

open import Data.List using(List;[];_∷_)
open import Relation.Nullary using (Dec;yes;no;¬_)

open import RegEx
open import Match

empty∣ :{A : Set}{l r : RegEx{A}} → ¬ Match l [] → ¬ Match r [] → ¬ Match (l ∣ r) []
empty∣ p1 p2 (dec1 x2) = p1 x2
empty∣ p1 p2 (dec2 x2) = p2 x2

empty∪1 :{A : Set}{l r : RegEx{A}} → ¬ Match l [] →  ¬ Match (l ⨁ r) [] 
empty∪1 p (con emp m1 m2) = p m1

empty∪2 :{A : Set}{l r : RegEx{A}} → ¬ Match r [] →  ¬ Match (l ⨁ r) [] 
empty∪2 p (con emp m1 m2) = p m2

empty :{A : Set} (r : RegEx{A}) → Dec (Match r [])
empty ∅ = no (λ ())
empty ε = yes eps
empty ⟦ c ⟧ = no (λ ())
empty (l ∣ r)   with empty l | empty r
empty (l ∣ r) | yes p        | p2       = yes (dec1 p)
empty (l ∣ r) | no ¬p        | yes p  = yes (dec2 p)
empty (l ∣ r) | no ¬p        | no ¬p1 = no (empty∣ ¬p ¬p1)
empty (l ⨁ r)   with empty l | empty r
empty (l ⨁ r) | yes p1       | yes p2 = yes (con emp p1 p2)
empty (l ⨁ r) | yes p1       | no ¬p2 = no (empty∪2 ¬p2)
empty (l ⨁ r) | no ¬p1       | p2     = no (empty∪1 ¬p1)
empty (r *) = yes (star (dec1 eps))
