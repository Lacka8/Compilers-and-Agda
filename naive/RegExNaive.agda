module RegExNaive where

open import Function using(_∘_;_∋_)
open import Relation.Nullary using(yes;no)
open import Data.Char using(Char;_≟_)
open import Data.Nat using(ℕ;zero;suc;_≤_;z≤n;s≤s;_+_;_⊔_)
open import Data.List using(List;[];_∷_;[_];map;concat;_++_;concatMap;foldr;length)--renaming(monad to monad)
open import Relation.Binary.PropositionalEquality using(_≡_;refl)
open import Data.Sum using(_⊎_) renaming(inj₁ to inj1;inj₂ to inj2)
open import Data.Product using(_×_;Σ;_,_) renaming(proj₁ to proj1;proj₂ to proj2)
open import Data.String using(toList)

--open import Category.Monad
--open import Agda.Primitive
--open RawMonad {lzero} monad
--monadic code looked uglz too so i left it this way

-- RegEx represents regular expressions with the smallest (?not sure about that) instructionset

data RegEx : Set where
 ε    : RegEx                   --emptystring
 char : Char  → RegEx           --1 specific character
 _⊹_ : RegEx → RegEx → RegEx   --concatenate 2 RegEx
 _*   : RegEx → RegEx           --Kleene star
 _∣_  : RegEx → RegEx → RegEx   --or decision

-- Split s s1 s2 can be formed if s = s1 ++ s2  

data Split {A : Set}: List A → List A → List A → Set where
 emp : {l : List A} → Split l [] l
 plus : {l1 l2 l : List A}{a : A} → Split l l1 l2 → Split (a ∷ l) (a ∷ l1) l2

-- splits makes all possible splits of a list and returns the 2 parts in a triple with a proof that they realz form the original list 

splits : {A : Set} → (s : List A) → List (Σ (List A × List A) ((λ { (s1 , s2) → Split s s1 s2 }))) 
splits [] = [ (([] , []) , emp) ]
splits  (x ∷ xs) = map (λ {((s1 , s2) , p) → ((x ∷ s1) , s2) , plus p}) (splits xs) ++ [ (([] , x ∷ xs) , emp) ]

-- What is important here is the new lists first element will be a split
--where the first list contains all the elements and therefore the second list is empty
--This is not used, but this way matching can be sped up by makeing this function evaluate lazily

-- This function is not used but it counts the maximum stepps it would take to match a regex on a string (not a proof just a calculation)

maxSteps : RegEx → List Char → ℕ
maxSteps ε _ = 1
maxSteps (char _) _ = 1
maxSteps (r1 ⊹ r2) s = suc(foldr _⊔_ 0 (map (λ {((s1 , s2), p) → maxSteps r1 s1 + maxSteps r2 s2}) (splits s)))
maxSteps (_ *) [] = 1
maxSteps (r *) (_ ∷ s) = suc (maxSteps (r *) s)
maxSteps (r1 ∣ r2) s = suc (maxSteps r1 s ⊔ maxSteps r2 s)

--A Match r l can be form if the Regex r accepts l 

data Match : RegEx → List Char → Set where
 empty : Match  ε []  
 char : {c1 c2 : Char} → c1 ≡ c2 → Match (char c2) [ c1 ]
 con : {s1 s2 s : List Char}{r1 r2 : RegEx} → Split s s1 s2  → Match r1 s1 → Match r2 s2 → Match (r1 ⊹ r2) s
 star0 : {r : RegEx} → Match (r *) []
 star' : {s s1 s2 : List Char}{a : Char}{r : RegEx} → Split (a ∷ s) (a ∷ s1) s2 → Match r (a ∷ s1) → Match (r *) s2  → Match (r *) (a ∷ s)
 choice : {s : List Char}{r1 r2 : RegEx} → (Match r1 s) ⊎ (Match r2 s) → Match (r1 ∣ r2) s

--See that the star' has to take at least 1 char at a time so ε* would terminate with a star0

--Couldnt find it in stl so wrote mz own
--should work as the haskells version 

unzip : {A B : Set} → (List A × List B) → List (A × B)
unzip ([] , b) = []
unzip (a ∷ as , []) = []
unzip (a ∷ as , b ∷ bs) = (a , b) ∷ (unzip (as , bs))

--This big boy takes care pf evrything when matching
-- the * and ⊹ deffinitions look ugly but couldnt find a way to make theme look nice

{-# TERMINATING #-}

matcher :(r : RegEx)  → (s : List Char) →  List (Match r s)
matcher ε []        = [ empty ]
matcher ε (_ ∷ _)   = []
matcher (char _) [] = []
matcher (char x) (c ∷ []) with c ≟ x
matcher (char x) (.x ∷ []) | yes refl = [ char refl ]
matcher (char _) (_ ∷ []) | no _      = []
matcher (char _) (_ ∷ _ ∷ _)          = []
matcher (_ *) [] = [ star0 ]
matcher (r *) (x ∷ xs) = concatMap
                          (λ {((s1 , s2), (m1 , m2 , p)) →
                             map
                             (λ {(a , b) → star' p a b})
                             (unzip (m1 , m2))})
                          (map
                            (λ {((s1 , s2), p) → (s1 , s2) , (matcher r (x ∷ s1) , matcher (r *) s2 , plus p)})
                            (splits xs))
matcher (r1 ⊹ r2) s = concatMap
                       (λ {((s1 , s2), (m1 , m2 , p)) →
                          map
                          (λ {(a , b) → con p a b})
                          (unzip (m1 , m2))})
                       ((map
                         (λ {((s1 , s2), p) → (s1 , s2) , matcher r1 s1 , matcher r2 s2 , p})
                         (splits s)))
matcher (r1 ∣ r2) s = map (choice ∘ inj1) (matcher r1 s) ++ map (choice ∘ inj2)  (matcher r2 s)

--some examples

reg1 : RegEx  -- /*a*/ type comment
reg1 = (char '/') ⊹ ((char '*') ⊹ (((((char 'a') ∣ char '/') ∣ (((char '*') ⊹ ((char '*') *)) ⊹ (char 'a'))) *) ⊹ (((char '*') ⊹ ((char '*') *)) ⊹ (char '/'))))

t1' : List(Match reg1 (toList "/*a*/"))
t1' = matcher reg1 (toList "/*a*/")
t2' = matcher reg1 (toList "/***/")
t3' = matcher reg1 (toList "/****/")
t4' = matcher reg1 (toList "/*a**a*/")
t5' = matcher reg1 (toList "/*a***/")
t6' = matcher reg1 (toList "/***a*/")
t7' = matcher reg1 (toList "/***a**a***/")

reg2 : RegEx
reg2 = (((char 'a') ⊹ (char 'a')) ∣ ((char 'a'))) *

t8' = matcher reg2 (toList "aa")

reg3 : RegEx
reg3 = ((char 'a') ∣ ((char 'a') ⊹ (char 'a')))*

t9' = matcher reg3 (toList "aa")

reg4 : RegEx
reg4 = ((char 'a') *) *

t10' = matcher reg4 (toList "aaaa")


t1 : List(Match reg1 (toList "/*a*/"))
t1 = matcher reg1 (toList "/*a*/")
t2 = matcher reg1 (toList "/***/")
t3 = matcher reg1 (toList "/****/")
t4 = matcher reg1 (toList "/*a**a*/")
t5 = matcher reg1 (toList "/*a***/")
t6 = matcher reg1 (toList "/***a*/")
t7 = matcher reg1 (toList "/***a**a***/")

reg5 = (char 'a' *) *

reg6 = ((char 'a' ⊹ char 'b') *) *


t11 = matcher reg5 (toList "aa")
t12 = matcher reg5 (toList "aaa")
t13 = matcher reg6 (toList "ababab")

{-
a** 
aaa

(aaa) (aa)(a) [(a)(aa)] (a)(a)(a)
-}
