module Problem1 where

{-
If we list all the natural numbers below 10 that are multiples of 3 or
5, we get 3, 5, 6 and 9. The sum of these multiples is 23.

Find the sum of all the multiples of 3 or 5 below 1000.
-}

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.List
open import Data.Sum

open import Relation.Unary.Properties
open import Relation.Binary.PropositionalEquality

problem′ : ℕ → ℕ
problem′ n = sum (filter ((3 ∣?_) ∪? (5 ∣?_)) (upTo n))

example : ℕ
example = problem′ 10

example-correct : example ≡ 23
example-correct = refl

-- this is actually quick enough but I'm sure we can do better
problem : ℕ
problem = problem′ 1000

module Lemmas where
  import Agda.Builtin.Nat
  open import Data.Bool using (true; false)
  open import Data.Empty
  open import Data.List.Properties
  open import Data.Nat.Properties
  open import Relation.Nullary

  -- first definition of triangle numbers. This is easiest to work with
  triangle : ℕ → ℕ
  triangle zero = zero
  triangle n@(suc x) = n + triangle x

  -- second definition of triangle numbers. This looks pretty but sadly ⌊_/2⌋
  -- is O(n) so this works out pretty slow in practice
  triangle′ : ℕ → ℕ
  triangle′ n = ⌊ n * suc n /2⌋

  -- Identity to do with adding to half something
  +-⌊n/⌋ : ∀ m n → m + ⌊ n /2⌋ ≡ ⌊ 2 * m + n /2⌋
  +-⌊n/⌋ zero n = refl
  +-⌊n/⌋ (suc m) n = begin
    suc (m + ⌊ n /2⌋)                  ≡⟨ cong suc (+-⌊n/⌋ m n) ⟩
    suc ⌊ 2 * m + n /2⌋                ≡⟨ cong (λ x → suc ⌊ m + x + n /2⌋) (+-identityʳ m) ⟩
    ⌊ suc (suc m + m) + n /2⌋          ≡˘⟨ cong (λ x → ⌊ suc x + n /2⌋) (+-suc m m) ⟩
    ⌊ suc (m + suc m + n) /2⌋          ≡˘⟨ cong (λ x → ⌊ suc (m + suc x + n) /2⌋) (+-identityʳ m) ⟩
    ⌊ suc (m + suc (m + zero) + n) /2⌋ ∎
    where
      open ≡-Reasoning

  -- The first two definitions of triangle numbers match!
  triangle≗triangle′ : triangle ≗ triangle′
  triangle≗triangle′ zero = refl
  triangle≗triangle′ (suc x) = begin
    triangle (suc x)            ≡⟨⟩
    suc x + triangle x          ≡⟨ cong (suc x +_) (triangle≗triangle′ x) ⟩
    suc x + triangle′ x         ≡⟨⟩
    suc x + ⌊ x * suc x /2⌋     ≡⟨ +-⌊n/⌋ (suc x) (x * suc x) ⟩
    ⌊ 2 * suc x + x * suc x /2⌋ ≡˘⟨ cong ⌊_/2⌋ (*-distribʳ-+ (suc x) 2 x) ⟩
    ⌊ (2 + x) * suc x /2⌋       ≡⟨ cong ⌊_/2⌋ (*-comm (2 + x) _) ⟩
    ⌊ suc x * suc (suc x) /2⌋   ≡⟨⟩
    triangle′ (suc x)           ∎
    where
      open ≡-Reasoning

  -- the third and final definition of triangle numbers
  -- This uses builtin division under the hood which gets compiled to proper
  -- division operators (I think ultimately GMP integer division) so it's fast
  triangle″ : ℕ → ℕ
  triangle″ n = n * suc n / 2

  -- halfing is the same as dividing by 2, as you might expect
  //2 : ∀ n → ⌊ n /2⌋ ≡ n / 2
  //2 zero = refl
  //2 (suc zero) = refl
  //2 (suc (suc n)) = begin
    suc ⌊ n /2⌋ ≡⟨ cong suc (//2 n) ⟩
    suc (n / 2) ≡˘⟨ +-distrib-/ 2 n (m%n<n n 1)  ⟩
    suc (suc n) / 2 ∎
    where
      open ≡-Reasoning

  -- the second and third definitions of triangle numbers also match!
  triangle′≗triangle″ : triangle′ ≗ triangle″
  triangle′≗triangle″ n = //2 _

  -- and so the first and thirdd definitions match
  triangle≗triangle″ : triangle ≗ triangle″
  triangle≗triangle″ x = trans (triangle≗triangle′ x) (triangle′≗triangle″ x)

  foo : ∀ {k m n j} → n ≤ j → Agda.Builtin.Nat.div-helper k m n j ≡ k
  foo z≤n = refl
  foo (s≤s p) = foo p

  m<n⇒m/n≡0 : ∀ {m n n≢0} → m < n → (m / n) {n≢0} ≡ 0
  m<n⇒m/n≡0 (s≤s p) = foo p

  ∣m∣n⇒∣m∸n : ∀ {i m n} → i ∣ m → i ∣ n → i ∣ m ∸ n
  ∣m∣n⇒∣m∸n {i} {m} {n} (divides quotient₁ equality) (divides quotient₂ equality₁) = divides (quotient₁ ∸ quotient₂) (begin
    m ∸ n ≡⟨ cong₂ _∸_ equality equality₁ ⟩
    quotient₁ * i ∸ quotient₂ * i ≡˘⟨ *-distribʳ-∸ i quotient₁ quotient₂ ⟩
    (quotient₁ ∸ quotient₂) * i ∎)
    where
      open ≡-Reasoning

  -- x * i = m
  -- y * i = n
  -- (x - y) * i = x * i - y * i = m - n

  lemma : {x d : ℕ} → suc d ∣ suc x → suc x / suc d ≡ suc (x / suc d)
  lemma {x} {zero} p = begin
    suc x / 1 ≡⟨ n/1≡n (suc x) ⟩
    suc x ≡˘⟨ cong suc (n/1≡n x) ⟩
    suc (x / 1) ∎
    where
      open ≡-Reasoning
  lemma {x} {suc d} (divides (suc q) p) = begin
    suc x / suc (suc d)                                         ≡⟨ cong (_/ suc (suc d)) p ⟩
    suc q * suc (suc d) / suc (suc d)                           ≡⟨ m*n/n≡m (suc q) (suc (suc d)) ⟩
    suc q                                                       ≡˘⟨ cong suc (m*n/n≡m q (suc (suc d))) ⟩
    suc (q * suc (suc d) / suc (suc d))                         ≡⟨⟩
    suc ((suc q ∸ 1) * suc (suc d) / suc (suc d))               ≡⟨ cong (λ x → suc (x / suc (suc d))) (*-distribʳ-∸ (suc (suc d)) (suc q) 1) ⟩
    suc ((suc q * suc (suc d) ∸ 1 * suc (suc d)) / suc (suc d)) ≡⟨ cong (λ x → suc ((suc q * suc (suc d) ∸ x) / suc (suc d))) (*-identityˡ (suc (suc d))) ⟩
    suc ((suc q * suc (suc d) ∸ suc (suc d)) / suc (suc d))     ≡˘⟨ cong (λ x → suc ((x ∸ suc (suc d)) / suc (suc d))) p ⟩
    suc (0 + (x ∸ suc d) / suc (suc d))                         ≡˘⟨ cong (λ n → suc (n + (x ∸ suc d) / suc (suc d))) (m<n⇒m/n≡0 (n<1+n (suc d))) ⟩
    suc (suc d / suc (suc d) + (x ∸ suc d) / suc (suc d))       ≡˘⟨ cong suc (+-distrib-/-∣ʳ {suc d} (x ∸ suc d) (∣m∣n⇒∣m∸n (divides (suc q) p) ∣-refl)) ⟩
    suc ((suc d + (x ∸ suc d)) / suc (suc d))                   ≡˘⟨ cong (λ x → suc (x / suc (suc d))) (+-∸-assoc (suc d) {x} {suc d} (+-cancelˡ-≤ 1 (≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (suc (suc d))))) (*-monoˡ-≤ (suc (suc d)) (s≤s {n = q} z≤n))) (≤-reflexive (sym p)))))⟩
    suc (((suc d + x) ∸ suc d) / suc (suc d))                   ≡⟨ cong (λ x → suc (x / suc (suc d))) (m+n∸m≡n (suc d) x) ⟩
    suc (x / suc (suc d)) ∎
    where
      open ≡-Reasoning

  open import Data.Product
  open import Data.Sum

  split-ℕ : ∀ n → n ≡ 0 ⊎ Σ ℕ (λ n′ → n ≡ suc n′)
  split-ℕ zero = inj₁ refl
  split-ℕ (suc n) = inj₂ (n , refl)

  bar : ∀ k j n x → j + k ≢ 0 → Agda.Builtin.Nat.mod-helper k (j + k) (suc n) j ≡ suc x → Agda.Builtin.Nat.mod-helper k (j + k) n j ≡ x
  bar k (suc j) zero x m≢0 p = +-cancelˡ-≡ 1 p
  bar zero zero (suc n) x m≢0 p = ⊥-elim (m≢0 refl)
  bar (suc k) zero (suc n) x m≢0 p = {!!}
  -- mod-helper (1+k) (1+k) (suc n) 0 ≡ suc x → mod-helper (1+k) (1+k) n 0 ≡ x
  -- mod-helper 0 (1+k) (suc n) (1+k) ≡ suc x → mod-helper 0 (1+k) n (1+k) ≡ x
  bar k (suc j) (suc n) x m≢0 p = {!!}

  sn%d≡sx⇒n%d≡x : ∀ {n d x} {d≢0} → (suc n % d) {d≢0} ≡ suc x → (n % d) {d≢0} ≡ x
  sn%d≡sx⇒n%d≡x {n} {suc d} {x} p = {!!}

  lemma₂ : {x d : ℕ} → ¬ (suc d ∣ suc x) → suc x / suc d ≡ x / suc d
  lemma₂ {x} {d} ¬p with split-ℕ (suc x % suc d)
  ... | inj₁ p = ⊥-elim (¬p (m%n≡0⇒n∣m _ _ p))
  ... | inj₂ (n , p) = begin
    suc x / suc d ≡⟨ +-distrib-/ 1 x {!!} ⟩
    1 / suc d + x / suc d ≡⟨ {!!} ⟩
    x / suc d     ∎
    where
      open ≡-Reasoning

  prop : ∀ d l → suc d * triangle (l / suc d) ≡ sum (filter (suc d ∣?_) (downFrom (suc l)))
  prop d zero = *-zeroʳ d
  prop d (suc l) with suc d ∣? suc l
  ... | true because ofʸ p = begin
    suc d * triangle (suc l / suc d)                         ≡⟨ cong (λ x → suc d * triangle x) (lemma p) ⟩
    suc d * triangle (suc (l / suc d))                       ≡⟨ *-distribˡ-+ (suc d) (suc (l / suc d)) (triangle (l / suc d)) ⟩
    suc d * (suc (l / suc d)) + suc d * triangle (l / suc d) ≡˘⟨ cong (λ x → suc d * x + suc d * triangle (l / suc d)) (lemma p) ⟩
    suc d * (suc l / suc d) + suc d * triangle (l / suc d)   ≡⟨ cong (_+ suc d * triangle (l / suc d)) (m*[n/m]≡n p) ⟩
    suc l + suc d * triangle (l / suc d)                     ≡⟨ cong (suc l +_) (prop d l) ⟩
    sum (suc l ∷ filter (suc d ∣?_) (downFrom (suc l)))      ≡˘⟨ cong sum (filter-accept (suc d ∣?_) p) ⟩
    sum (filter (suc d ∣?_) (suc l ∷ downFrom (suc l)))      ∎
    where
      open ≡-Reasoning
  ... | false because ofⁿ ¬p = begin
    suc d * triangle (suc l / suc d) ≡⟨ cong (λ n → suc d * triangle n) (lemma₂ ¬p) ⟩
    suc d * triangle (l / suc d) ≡⟨ prop d l ⟩
    sum (filter (suc d ∣?_) (downFrom (suc l))) ≡˘⟨ cong sum (filter-reject (suc d ∣?_) ¬p) ⟩
    sum (filter (suc d ∣?_) (suc l ∷ downFrom (suc l))) ∎
    where
      open ≡-Reasoning

solution′ : ℕ → ℕ
solution′ zero = zero
solution′ (suc n) = 3 * Lemmas.triangle″ (n / 3) + 5 * Lemmas.triangle″ (n / 5) ∸ 15 * Lemmas.triangle″ (n / 15)

{-
solution-correct : problem′ ≗ solution′
solution-correct zero = refl
solution-correct (suc n) = {!!}
-}

solution : ℕ
solution = solution′ 1000

-- output the solution
open import Data.Nat.Show
open import IO
import IO.Primitive as Prim

main : Prim.IO _
main = run (putStrLn (show solution))
