module RegEx where

data RegEx {A : Set} : Set where
 ∅    : RegEx
 ε    : RegEx
 ⟦_⟧  : A  → RegEx
 _∣_  : RegEx {A} → RegEx {A} → RegEx
 _⨁_  : RegEx {A} → RegEx {A} → RegEx
 _*   : RegEx {A} → RegEx
