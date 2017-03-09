module RegEx where

open import Function using(_∘_;_∋_)
open import Relation.Nullary using(yes;no)
open import Data.Char using(Char;_≟_)
open import Data.Nat using(ℕ;zero;suc;_≤_;z≤n;s≤s)
open import Data.List using(List;[];_∷_;[_];map;concat;_++_;concatMap)
open import Relation.Binary.PropositionalEquality using(_≡_;refl)
open import Data.Sum using(_⊎_) renaming(inj₁ to inj1;inj₂ to inj2)
open import Data.Product using(_×_;Σ;_,_) renaming(proj₁ to proj1;proj₂ to proj2)
open import Data.String using(toList)

data RegEx : Set where
 char : Char → RegEx
 _∪_ : RegEx → RegEx → RegEx
 _* : RegEx → RegEx
 _∣_ : RegEx → RegEx → RegEx

data Split {A : Set}: List A → List A → List A → Set where
 zero : {l : List A} → Split l [] l
 suc : {l1 l2 l : List A}{a : A} → Split l l1 l2 → Split (a ∷ l) (a ∷ l1) l2

data Match : RegEx → List Char → Set where
 char : {c1 c2 : Char} → c1 ≡ c2 → Match (char c2) [ c1 ]
 con : {s1 s2 s : List Char}{r1 r2 : RegEx} → Split s s1 s2  → Match r1 s1 → Match r2 s2 → Match (r1 ∪ r2) s
 star0 : {r : RegEx} → Match (r *) []
 star' : {s s1 s2 : List Char}{a : Char}{r : RegEx} → Split (a ∷ s) (a ∷ s1) s2 → Match r (a ∷ s1) → Match (r *) s2  → Match (r *) (a ∷ s)
 choice : {s : List Char}{r1 r2 : RegEx} → (Match r1 s) ⊎ (Match r2 s) → Match (r1 ∣ r2) s

splits : {A : Set} → (s : List A) → List (Σ (List A × List A) ((λ { (s1 , s2) → Split s s1 s2 }))) 
splits [] = [ (([] , []) , zero) ]
splits  (x ∷ xs) = map (λ {((s1 , s2) , p) → ((x ∷ s1) , s2) , suc p}) (splits xs) ++ [ (([] , x ∷ xs) , zero) ]

unzip : {A B : Set} → (List A × List B) → List (A × B)
unzip ([] , b) = []
unzip (a ∷ as , []) = []
unzip (a ∷ as , b ∷ bs) = (a , b) ∷ (unzip (as , bs))

{-# TERMINATING #-}

matcher' : (r : RegEx)  → (s : List Char) →  List (Match r s)
matcher' (char x) [] = []
matcher' (char x) (c ∷ [])  with c ≟ x
matcher' (char x) (c ∷ [])  | yes p = [ char p ]
matcher' (char x) (c ∷ [])  | no ¬p = []
matcher' (char x) (c1 ∷ c2 ∷ cs)  = []
matcher' (r *) [] = [ star0 ]
matcher' (r *) (x ∷ xs) = concatMap
  (λ {((s1 , s2), (m1 , m2 , p)) → map (λ {(a , b) → star' p a b}) (unzip (m1 , m2))})
  ( List (Σ (List Char × List Char) (λ {(st , st2) → List (Match r (x ∷ st)) × List (Match (r *) st2) × Split (x ∷ xs) (x ∷ st) st2})) ∋ (map
   (λ {((s1 , s2), p) → (s1 , s2) , (matcher' r (x ∷ s1) , matcher' (r *) s2 , suc p)})
   (splits xs)))
matcher' (r1 ∪ r2) s = concatMap (λ {((s1 , s2), (m1 , m2 , p)) → map (λ {(a , b) → con p a b}) (unzip (m1 , m2))}) ((map (λ {((s1 , s2), p) → (s1 , s2) , matcher' r1 s1 , matcher' r2 s2 , p}) (splits s)))
matcher' (r1 ∣ r2) s with matcher' r1 s | matcher' r2 s
... | l1 | l2 = map (choice ∘ inj1) l1 ++ map (choice ∘ inj2) l2


reg1 : RegEx  -- /*a*/ type comment
reg1 = (char '/') ∪ ((char '*') ∪ (((((char 'a') ∣ char '/') ∣ (((char '*') ∪ ((char '*') *)) ∪ (char 'a'))) *) ∪ (((char '*') ∪ ((char '*') *)) ∪ (char '/'))))

t1 : List(Match reg1 (toList "/*a*/"))
t1 = matcher' reg1 (toList "/*a*/")

t2 = matcher' reg1 (toList "/***/")
t3 = matcher' reg1 (toList "/****/")
t4 = matcher' reg1 (toList "/*a**a*/")
t5 = matcher' reg1 (toList "/*a***/")
t6 = matcher' reg1 (toList "/***a*/")
t7 = matcher' reg1 (toList "/***a**a***/")

reg2 : RegEx
reg2 = (((char 'a') ∪ (char 'a')) ∣ ((char 'a'))) *

t8 = matcher' reg2 (toList "aa")

reg3 : RegEx
reg3 = ((char 'a') ∣ ((char 'a') ∪ (char 'a')))*

t9 = matcher' reg3 (toList "aa")
