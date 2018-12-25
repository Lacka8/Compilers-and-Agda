module RegEx where

data RegEx (A : Set) : Set where
 ∅    : RegEx A
 ε    : RegEx A
 ⟦_⟧  : A  → RegEx A
 _∣_  : RegEx A → RegEx A → RegEx A
 _⨁_  : RegEx A → RegEx A → RegEx A
 _*   : RegEx A → RegEx A
