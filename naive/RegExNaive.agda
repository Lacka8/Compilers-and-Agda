module RegExNaive where

open import Relation.Nullary using(yes;no)
open import Data.Char using(Char)
open import Data.Char.Unsafe using(_≟_)
open import Data.List using(List;[];_∷_;[_];map;concat;_++_)
open import Relation.Binary.PropositionalEquality using(refl)
open import Data.Product using(_×_;Σ;_,_)
open import Data.String using(toList)

-- RegEx represents regular expressions

data RegEx : Set where
 ⊘ : RegEx
 ε     : RegEx                   --emptystring
 ⟦_⟧  : Char  → RegEx           --1 specific character
 _⊕_ : RegEx → RegEx → RegEx   --concatenate 2 RegEx
 _∣_  : RegEx → RegEx → RegEx   --or decision
 _*   : RegEx → RegEx           --Kleene star

-- Split is inroduced for pattern matching and so we dont have to prove list concatenations

data Split {A : Set}: List A → List A → List A → Set where
 emp : {l : List A} → Split l [] l
 add : {l1 l2 l : List A}{a : A} → Split l l1 l2 → Split (a ∷ l) (a ∷ l1) l2

-- Match represents a possible way for a RegEx to accept a string ( there might be multiple )

data Match : RegEx → List Char → Set where
 empty : Match  ε []  
 char : {c : Char} → Match ⟦ c ⟧ [ c ]
 con : {s1 s2 s : List Char}{r1 r2 : RegEx} → Split s s1 s2  → Match r1 s1 → Match r2 s2 → Match (r1 ⊕ r2) s
 star0 : {r : RegEx} → Match (r *) []
 star' : {s s1 s2 : List Char}{a : Char}{r : RegEx} → Split (a ∷ s) (a ∷ s1) s2 → Match r (a ∷ s1) → Match (r *) s2  → Match (r *) (a ∷ s)
 choice1 : {s : List Char}{r1 r2 : RegEx} → (Match r1 s) → Match (r1 ∣ r2) s
 choice2 : {s : List Char}{r1 r2 : RegEx} → (Match r2 s) → Match (r1 ∣ r2) s

-- creates all Splits for a list (maybe split can be modified so we donr have to use dependent pairs)

splits : (l : List Char) → List (Σ (List Char × List Char) ((λ { (s1 , s2) → Split l s1 s2 })))
splits [] = [ (([] , []) , emp) ]
splits (x ∷ xs) = ((([] , (x ∷ xs)) , emp)) ∷ map (λ { ((s1 , s2) , s) → ((x ∷ s1) , s2) , (add s)}) (splits xs) where

-- all possible combinations

combine : {A B : Set} → List A → List B → List (A × B)
combine [] ys = []
combine (x ∷ xs) ys = map (_,_ x) ys ++ combine xs ys

-- The matcher itself
-- Agda somehow cant proove termination ???

{-# TERMINATING #-}

match : (l : List Char) → (r : RegEx) → List (Match r l)
match l ⊘ = []
match [] ε = [ empty ]
match (x ∷ xs) ε = []
match [] ⟦ c ⟧ = []
match (x ∷ []) ⟦ c ⟧ with c ≟ x
match (x ∷ []) ⟦ .x ⟧ | yes refl = [ char  ]
match (x ∷ []) ⟦ c ⟧ | no ¬p = []
match (x1 ∷ x2 ∷ xs) ⟦ c ⟧ = []
match l (r1 ⊕ r2) = concat (map allCons (splits l)) where
  allCons : Σ (List Char × List Char) (λ { (s1 , s2) → Split l s1 s2 }) → List (Match (r1 ⊕ r2) l)
  allCons ((s1 , s2) , s) = map (λ { (m1 , m2) → con s m1 m2}) (combine (match  s1 r1) (match s2 r2))
match l (r1 ∣ r2) = (map choice1 (match l r1)) ++ map choice2 (match l r2)
match [] (r *) = star0 ∷ []
match (x ∷ xs) (r *) = concat (map allStar (splits xs)) where
  allStar : Σ (List Char × List Char) (λ { (s1 , s2) → Split xs s1 s2 }) → List (Match (r *) (x ∷ xs))
  allStar ((s1 , s2) , s) = map (λ { (m1 , m2) → star' (add s) m1 m2}) (combine (match (x ∷ s1) r) (match s2 (r *)))
