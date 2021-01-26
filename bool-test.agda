module bool-test where

open import bool
open import eq
open import level

~~tt : ~ ~ tt ≡ tt
~~tt = refl

~~ff : ~ ~ ff ≡ ff
~~ff = refl

~~-elim2 : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim2 tt = ~~tt
~~-elim2 ff = ~~ff

elim3 : ∀ (b : 𝔹) → ~ ~ b ≡ b
elim3 tt = refl
elim3 ff = refl

~~tt' : ~ ~ tt ≡ tt
~~tt' = refl{lzero}{𝔹}{tt}

~~ff' : ~ ~ ff ≡ ff
~~ff' = refl{lzero}{𝔹}{ff}

test1 : 𝔹
test1 = tt && ff

test2 : 𝔹
test2 = tt && tt

test1-ff : test1 ≡ ff
test1-ff = refl

test2-tt : test2 ≡ tt
test2-tt = refl

&&-idem : ∀ (b : 𝔹) → b && b ≡ b
&&-idem tt = refl
&&-idem ff = refl


||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ ff → ff ≡ b1
||≡ff₁ {ff} p = refl
||≡ff₁ {tt} p = sym p 

||cong1 : ∀ {b1 b1' b2} → (b1 ≡ b1') → (b1 || b2) ≡ b1' || b2
||cong1 {b1} {b1'} {b2} refl = refl

||cong2 : ∀ {b1 b2 b2'} → (b2 ≡ b2') → (b1 || b2) ≡ b1 || b2'
||cong2 p rewrite p = refl

ite-same : ∀ {a}{A : Set a} → ∀ (b : 𝔹) (x : A) → (if b then x else x) ≡ x
ite-same tt x = refl
ite-same ff x = refl

contradiction : ff ≡ tt → ∀ {P : Set} → P
contradiction ()
