module RegExNaiveVec where

open import Function using(_∘_;_∋_)
open import Relation.Nullary using(yes;no)
open import Data.Char using(Char;_≟_)
open import Data.Nat using(ℕ;zero;suc;_≤_;z≤n;s≤s;_+_;_⊔_)
--open import Data.List using(List;[];_∷_;[_];map;concat;_++_;concatMap;foldr;length)--renaming(monad to monad)
open import Relation.Binary.PropositionalEquality using(_≡_;refl)
open import Data.Sum using(_⊎_) renaming(inj₁ to inj1;inj₂ to inj2)
open import Data.Product using(_×_;Σ;_,_) renaming(proj₁ to proj1;proj₂ to proj2)
open import Data.String using(toList)
open import Data.Vec using(Vec;[];_∷_;[_];map;_++_;fromList)

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

data Split {A : Set}: {n m : ℕ} → Vec A (n + m) → Vec A n → Vec A m → Set where
 emp : {n : ℕ}{v : Vec A n} → Split v [] v
 plus : {n m : ℕ}{v1 : Vec A n}{v2 : Vec A m}{v : Vec A (n + m)}{a : A} → Split v v1 v2 → Split (a ∷ v) (a ∷ v1) v2

-- splits makes all possible splits of a list and returns the 2 parts in a triple with a proof that they realz form the original list 

Splitlet : {A : Set} → {n : ℕ} → Vec A n → Set
Splitlet {A} {n} v = (Σ (ℕ × ℕ) (λ {(a , b) → Σ ((Vec A a) × (Vec A b) × ((a + b) ≡ n)) (λ { (v1 , v2 , refl) → Split {A} {a} {b} v v1 v2})}))


Splits : {A : Set} → {n : ℕ}→ Vec A n → Set
Splits {A} {n} v = Vec (Splitlet v) (suc n)

suffix : {n : ℕ} → {A : Set} → (v : Vec A n) → Splitlet v
suffix {n} v = (0 , n) , (([] , (v , refl)) , emp)

append : {n : ℕ} → {A : Set} → {xs : Vec A n} → (x : A) → Splitlet xs → Splitlet (x ∷ xs)
append {n} {xs = xs} x s = (1 , n) , (x ∷ [] , (xs , refl)) , plus emp

splits : {n : ℕ} → {A : Set} → (v : Vec A n) → Splits v
splits [] = ((0 , 0) , ([] , [] , refl) , emp) ∷ []
splits {n} (x ∷ xs) =   (suffix (x ∷ xs))  ∷ (map (append x) (splits xs))

--Vec (Σ (ℕ × ℕ) (λ {(a , b) →(n ≡ (a + b) × Σ (Vec A a × Vec A b) (λ { (s1 , s2) → Split s s1 s2 }))})) 
--splits [] = [ (([] , []) , emp) ]
--splits  (x ∷ xs) = map (λ {((s1 , s2) , p) → ((x ∷ s1) , s2) , plus p}) (splits xs) ++ [ (([] , x ∷ xs) , emp) ]

{-

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
-}
