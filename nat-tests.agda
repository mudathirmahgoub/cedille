module nat-tests where

open import bool
open import eq
open import nat
open import nat-division
open import nat-to-string
open import product

{- you can prove x + 0 ≡ x and 0 + x ≡ x without induction, if you
   use this more verbose definition of addition: -}
_+a_ : ℕ → ℕ → ℕ
0 +a 0 = 0
(suc x) +a 0 = (suc x)
0 +a (suc y) = (suc y)
(suc x) +a (suc y) = suc (suc (x +a y))

0+a : ∀ (x : ℕ) → x +a 0 ≡ x
0+a 0 = refl
0+a (suc y) = refl

+a0 : ∀ (x : ℕ) → 0 +a x ≡ x
+a0 0 = refl
+a0 (suc y) = refl

8-div-3-lem : 8 ÷ 3 !! refl ≡ 2 , 2
8-div-3-lem = refl

23-div-5-lem : 23 ÷ 5 !! refl ≡ 4 , 3 
23-div-5-lem = refl

ℕ-to-string-lem : ℕ-to-string 237 ≡ "237"
ℕ-to-string-lem = refl


0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 0                    = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ)  → x + (y + z) ≡ (x + y) + z
+assoc zero y z      = refl
+assoc (suc x) y z rewrite +assoc x y z = refl


+suc : ∀ (x y : ℕ) → x + (suc y) ≡ suc(x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+comm :  ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x) y rewrite +comm x y | +suc y x = refl
--+comm (suc x) y rewrite +suc y x |  +comm x y = refl

*distribr : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*distribr zero y z = refl
*distribr (suc x) y z rewrite *distribr x y z = +assoc z (x * z) (y * z)

*0 : ∀ (x : ℕ) → x * 0 ≡ 0
*0 0                    = refl
*0 (suc x) rewrite *0 x = refl

*suc : ∀ (x y : ℕ) → x * (suc y) ≡ x + x * y
*suc zero y = refl
*suc (suc x) y rewrite *suc x y | +assoc y x (x * y) | +comm y x | +assoc x y (x * y) = refl

*comm :  ∀ (x y : ℕ) → x * y ≡ y * x
*comm zero y rewrite *0 y = refl
*comm (suc x) y rewrite *suc y x | *comm x y = refl



-- (y + (x + x *y)) = ((y+x) + x * y) = ((x + y) + x * y) = x + (y + x * y)

*assoc : ∀ (x y z : ℕ)  → x * (y * z) ≡ (x * y) * z
*assoc zero y z = refl
*assoc (suc x) y z rewrite *distribr y (x * y) z | *assoc x y z = refl

<-0 : ∀ (x : ℕ) → x < 0 ≡ ff
<-0 zero = refl
<-0 (suc x) = refl


aux0 : ∀ {x y : ℕ} → suc x < suc y ≡ tt → x < y ≡ tt
aux0 {zero} {y} p  = p
aux0 {suc x} {y} p = p


𝔹-contra : ff ≡ tt → ∀{ℓ} {P : Set ℓ} → P
𝔹-contra ()

<-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
<-trans {x} {0} p1 p2 rewrite <-0 x  = 𝔹-contra p1
<-trans {0} {suc y} {0} p1 p2  = 𝔹-contra p2
<-trans {0} {suc y} {suc z} p1 p2 = refl
<-trans {suc x} {suc y} {0} p1 p2 = 𝔹-contra p2
<-trans {suc x} {suc y} {suc z} p1 p2 rewrite <-trans {x} {y} {z} p1 p2 = refl
-- <-trans {suc x} {suc y} {suc z} p1 p2 = <-trans {x} {y} {z} p1 p2

=ℕ-refl : ∀ (x : ℕ) → (x =ℕ x) ≡ tt
=ℕ-refl zero = refl
=ℕ-refl (suc x) = =ℕ-refl x

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ tt → x ≡ y
--=ℕ-to-≡ {x} p  = {!!}
=ℕ-to-≡ {zero} {zero} p = refl
=ℕ-to-≡ {suc x} {suc y} p rewrite =ℕ-to-≡ {x} {y} p = refl
=ℕ-to-≡ {zero} {suc y} ()
=ℕ-to-≡ {suc x} {zero} ()

=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y  → x =ℕ y ≡ tt
=ℕ-from-≡ {x} refl = =ℕ-refl x

is-even2 : ℕ → 𝔹
is-even2 zero = tt
is-even2 (suc zero) = ff
is-even2 (suc (suc m)) = is-even2 m

is-odd2 : ℕ → 𝔹
is-odd2 zero = ff
is-odd2 (suc zero) = tt
is-odd2 (suc (suc m)) = is-odd2 m


is-even2≡is-even : ∀ (n : ℕ) → (is-even2 n ≡ tt) ≡ (is-even n ≡ tt)
is-even2≡is-even zero = refl
is-even2≡is-even (suc zero) = refl
is-even2≡is-even (suc (suc n)) =  is-even2≡is-even n

even~odd : ∀ (x : ℕ) → is-even x ≡ ~ is-odd x
odd~even : ∀ (x : ℕ) → is-odd x ≡ ~ is-even x
even~odd zero = refl
even~odd (suc x) = odd~even x
odd~even zero = refl
odd~even (suc x) = even~odd x
