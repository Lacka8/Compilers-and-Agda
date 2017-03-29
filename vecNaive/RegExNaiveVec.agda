module RegExNaiveVec where

open import Function using(_∘_{-;_∋_-})
open import Relation.Nullary using(yes;no)
open import Data.Char using(Char;_≟_)
open import Data.Nat using(ℕ;zero;suc;_+_)
open import Data.List using(List;[];_∷_;concatMap) renaming (map to mapL;_++_ to _+l+_)--renaming(monad to monad)
open import Relation.Binary.PropositionalEquality using(_≡_;refl;cong;subst;sym)-- renaming (cong to cong≡)
open import Data.Sum using(_⊎_) renaming(inj₁ to inj1;inj₂ to inj2)
open import Data.Product using(_×_;Σ;_,_) renaming(proj₁ to proj1;proj₂ to proj2)
open import Data.String using(toList)
open import Data.Vec using(Vec;[];_∷_;[_];map;_++_;fromList;reverse) renaming (toList to vecToList)

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

--split : {A : Set} → {n a b : ℕ} → (v : Vec A n) → (v1 : Vec A a) → (v2 : Vec A b) → (a + b) ≡ n → Split v v1 v2
--split = ?
{-
record Splitlet {A : Set}{n : ℕ} :  Set where
  constructor splitlet 
  field
    v : Vec A n
    a : ℕ
    b : ℕ
    e : (a + b) ≡ n
    v1 : Vec A a
    v2 : Vec A b
    spl : Split {!!} v1 v2
-}

Splits : {A : Set} → {n : ℕ}→ Vec A n → Set
Splits {A} {n} v = Vec (Splitlet v) (suc n)

suffix : {n : ℕ} → {A : Set} → (v : Vec A n) → Splitlet v
suffix {n} v = (0 , n) , (([] , (v , refl)) , emp)

append : {n : ℕ} → {A : Set} → {xs : Vec A n} → (x : A) → Splitlet xs → Splitlet (x ∷ xs)
append {.(a + b)} {xs = xs} x ((a , b) , (s1 , s2 , refl) , p) = (suc a , b) , (x ∷ s1 , (s2 , refl)) , plus p

n+sm=sn+m : (n m : ℕ) → n + (suc m) ≡ (suc n) + m
n+sm=sn+m zero m = refl
n+sm=sn+m (suc n) m = cong suc (n+sm=sn+m n m)

+comm : (n m : ℕ) → n + m ≡ m + n
+comm zero zero = refl
+comm zero (suc m) = cong suc (+comm zero m)
+comm (suc n) m = subst (λ x → suc (n + m) ≡ x) (sym (n+sm=sn+m m n)) (cong suc (+comm n m))

--splits : {n : ℕ} → {A : Set} → (v : Vec A n) → Splits v
--splits [] = (suffix []) ∷ []
--splits {n} (x ∷ xs) = (map (append x) (splits xs)) ++ [ (suffix (x ∷ xs)) ]

splits' : {n : ℕ} → {A : Set} → (v : Vec A n) → Splits v
splits' [] = (suffix []) ∷ []
splits' {n} (x ∷ xs) = (suffix (x ∷ xs)) ∷ (map (append x) (splits' xs))

splits : {n : ℕ} → {A : Set} → (v : Vec A n) → Splits v
splits v = reverse (splits' v) 



-- What is important here is the new lists first element will be a split
--where the first list contains all the elements and therefore the second list is empty
--This is not used, but this way matching can be sped up by makeing this function evaluate lazily

--A Match r l can be form if the Regex r accepts l 

data Match : RegEx → {n : ℕ} → Vec Char n → Set where
 empty : Match  ε []  
 char : {c1 c2 : Char} → c1 ≡ c2 → Match (char c2) [ c1 ]
 con : {n m : ℕ}{s1 : Vec Char n}{s2 : Vec Char m}{s : Vec Char (n + m)}{r1 r2 : RegEx} → Split s s1 s2  → Match r1 s1 → Match r2 s2 → Match (r1 ⊹ r2) s
 star0 : {r : RegEx} → Match (r *) []
 star' : {n m : ℕ}{s1 : Vec Char n}{s2 : Vec Char m}{s : Vec Char (n + m)}{a : Char}{r : RegEx} → Split (a ∷ s) (a ∷ s1) s2 → Match r (a ∷ s1) → Match (r *) s2  → Match (r *) (a ∷ s)
 choice : {n : ℕ}{s : Vec Char n}{r1 r2 : RegEx} → (Match r1 s) ⊎ (Match r2 s) → Match (r1 ∣ r2) s

--See that the star' has to take at least 1 char at a time so ε* would terminate with a star0

unzip : {A B : Set} → (List A × List B) → List (A × B)
unzip ([] , b) = []
unzip (a ∷ as , []) = []
unzip (a ∷ as , b ∷ bs) = (a , b) ∷ (unzip (as , bs))

--This big boy takes care pf evrything when matching
-- the * and ⊹ deffinitions look ugly but couldnt find a way to make theme look nice
mutual

  matcher : {n : ℕ} → (r : RegEx)  → (s : Vec Char n) →  List (Match r s)
  matcher ε [] = empty ∷ []
  matcher ε (x ∷ s) = []
  matcher (char c) [] = []
  matcher (char c) (x ∷ []) with x ≟ c
  matcher (char c) (.c ∷ []) | yes refl = (char refl) ∷ []
  matcher (char c) (x ∷ []) | no ¬p = []
  matcher (char c) (_ ∷ _ ∷ _) = []
  matcher (r1 ⊹ r2) s = concatMap {!(λ {(ms , p) → mapL (λ {(m1 , m2) → con p m1 m2}) (unzip ms)})!} (mapL (λ {((a , b) , (s1 , s2 , e) , p) → {!!}}) ((vecToList (splits s))))
  matcher (r *) s = {!!}
  matcher (r1 ∣ r2) s = (mapL (choice ∘ inj1) (matcher r1 s)) +l+ mapL (choice ∘ inj2) (matcher r2 s)

--  splitMatcher : {n : ℕ} → (r1 r2 : RegEx) → (v : Vec Char n) → List (Σ (Splitlet v) (λ {((_ , _) , (s1 , s2 , refl) , _) → List (Match r1 s1) × List (Match r2 s2)}))
 -- splitMatcher r1 r2 v = mapL (λ { ((a , b) , (s1 , s2 , e) , p) → {!!}}) (vecToList (splits v))
--(λ {((a , b) , (s1 , s2 , e) , p) → ((a , b) , (s1 , (s2 , e)) , p) , matcher r1 s1 , matcher r2 s2 , ?})
{-
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
