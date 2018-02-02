module Match where

open import Data.List using(List;[];_∷_;[_];_++_)

open import RegEx

data Split {A : Set}: List A → List A → List A → Set where
 emp : {l : List A} → Split l [] l
 add : {l l1 l2 : List A}{a : A} → Split l l1 l2 → Split (a ∷ l) (a ∷ l1) l2

data Match {A : Set}: RegEx → List A → Set where
 eps  : Match ε []
 char : {c : A} → Match ⟦ c ⟧ [ c ]
 dec1 : {l r : RegEx}{s : List A} → Match l s → Match (l ∣ r) s 
 dec2 : {l r : RegEx}{s : List A} → Match r s → Match (l ∣ r) s 
 con  : {l r : RegEx}{s s1 s2 : List A} → Split s s1 s2 → Match l s1 → Match  r s2 → Match (l ⨁ r) s
 star : {r : RegEx}{s : List A} → Match (ε ∣ (r ⨁ (r *))) s → Match (r *) s


unSplit : {A : Set}(t1 t2 : List A) → Split (t1 ++ t2) t1 t2
unSplit [] t2 = emp
unSplit (x ∷ t1) t2 = add (unSplit t1 t2)
