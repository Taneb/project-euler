module Problem1 where

{-
If we list all the natural numbers below 10 that are multiples of 3 or
5, we get 3, 5, 6 and 9. The sum of these multiples is 23.

Find the sum of all the multiples of 3 or 5 below 1000.
-}

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.List
open import Data.Sum

open import Function.Nary.NonDependent using (congₙ)

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

  open import Algebra.Definitions

  open import Data.Bool using (true; false)
  open import Data.Empty
  open import Data.List.Properties
  open import Data.Nat.LCM

  open import Relation.Nullary
  open import Relation.Unary

  -- first definition of triangle numbers. This is easiest to work with
  triangle : ℕ → ℕ
  triangle zero = zero
  triangle n@(suc x) = n + triangle x

  -- second definition of triangle numbers. This looks pretty but sadly ⌊_/2⌋
  -- is O(n) so this works out pretty slow in practice
  triangle′ : ℕ → ℕ
  triangle′ n = ⌊ n * suc n /2⌋

  -- Identity to do with adding to half something
  +-⌊n/2⌋ : ∀ m n → m + ⌊ n /2⌋ ≡ ⌊ 2 * m + n /2⌋
  +-⌊n/2⌋ zero n = refl
  +-⌊n/2⌋ (suc m) n = begin
    suc (m + ⌊ n /2⌋)         ≡⟨ cong suc (+-⌊n/2⌋ m n) ⟩
    suc ⌊ 2 * m + n /2⌋       ≡⟨ cong (λ x → suc ⌊ m + x + n /2⌋) (+-identityʳ m) ⟩
    ⌊ suc (suc m + m) + n /2⌋ ≡˘⟨ cong (λ x → ⌊ suc x + n /2⌋) (+-suc m m) ⟩
    ⌊ suc (m + suc m + n) /2⌋ ≡˘⟨ cong (λ x → ⌊ suc (m + suc x + n) /2⌋) (+-identityʳ m) ⟩
    ⌊ 2 * suc m + n /2⌋       ∎
    where
      open ≡-Reasoning

  -- The first two definitions of triangle numbers match!
  triangle≗triangle′ : triangle ≗ triangle′
  triangle≗triangle′ zero = refl
  triangle≗triangle′ (suc x) = begin
    triangle (suc x)            ≡⟨ cong (suc x +_) (triangle≗triangle′ x) ⟩
    suc x + ⌊ x * suc x /2⌋     ≡⟨ +-⌊n/2⌋ (suc x) (x * suc x) ⟩
    ⌊ 2 * suc x + x * suc x /2⌋ ≡˘⟨ cong ⌊_/2⌋ (*-distribʳ-+ (suc x) 2 x) ⟩
    ⌊ (2 + x) * suc x /2⌋       ≡⟨ cong ⌊_/2⌋ (*-comm (2 + x) _) ⟩
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

  -- if we're almost done dividing, we're not going to change the answer
  foo : ∀ {k m n j} → n ≤ j → Agda.Builtin.Nat.div-helper k m n j ≡ k
  foo z≤n = refl
  foo (s≤s p) = foo p

  -- dividing a small number by a big one gets 0
  m<n⇒m/n≡0 : ∀ {m n n≢0} → m < n → (m / n) {n≢0} ≡ 0
  m<n⇒m/n≡0 (s≤s p) = foo p

  -- if i divides both m and n then it divides their difference
  ∣m∣n⇒∣m∸n : ∀ {i m n} → i ∣ m → i ∣ n → i ∣ m ∸ n
  ∣m∣n⇒∣m∸n (divides p refl) (divides q refl) = divides (p ∸ q) (sym (*-distribʳ-∸ _ p q))

  lemma : {x d : ℕ} → suc d ∣ suc x → suc x / suc d ≡ suc (x / suc d)
  lemma {x} {zero} p = begin
    suc x / 1   ≡⟨ n/1≡n (suc x) ⟩
    suc x       ≡˘⟨ cong suc (n/1≡n x) ⟩
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
    suc ((suc d + (x ∸ suc d)) / suc (suc d))                   ≡˘⟨ cong (λ x → suc (x / suc (suc d))) (+-∸-assoc (suc d) (+-cancelˡ-≤ 1 (≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (suc (suc d))))) (*-monoˡ-≤ (suc (suc d)) (s≤s {n = q} z≤n))) (≤-reflexive (sym p)))))⟩
    suc (((suc d + x) ∸ suc d) / suc (suc d))                   ≡⟨ cong (λ x → suc (x / suc (suc d))) (m+n∸m≡n (suc d) x) ⟩
    suc (x / suc (suc d)) ∎
    where
      open ≡-Reasoning

  bar : ∀ {x d} → ¬ (suc (suc d) ∣ suc x) → x % suc (suc d) ≤ d
  bar {x} {d} ¬p with suc x % suc (suc d) | inspect (λ a → a % suc (suc d)) (suc x)
  ... | zero  | [ p ] = ⊥-elim (¬p (m%n≡0⇒n∣m (suc x) (suc d) p))
  ... | suc n | [ p ] = [1+m%d]≤1+n⇒[m%d]≤n x d (suc (suc d)) (≤-trans (s≤s z≤n) (≤-reflexive (sym p))) (+-cancelˡ-≤ 1 (m%n<n (suc x) (suc d)))

  lemma₂ : {x d : ℕ} → ¬ (suc d ∣ suc x) → suc x / suc d ≡ x / suc d
  lemma₂ {x} {zero} ¬p = ⊥-elim (¬p (1∣ suc x))
  lemma₂ {x} {suc d} ¬p with suc x % suc (suc d) | inspect (λ a → a % suc (suc d)) (suc x)
  ... | zero  | [ p ] = ⊥-elim (¬p (m%n≡0⇒n∣m _ _ p))
  ... | suc n | [ p ] = +-distrib-/ 1 x (+-monoʳ-≤ 2 (bar ¬p))

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

  notLemmaAux : ∀ {A : Set} (∙ : A → A → A) (ε : A) (comm : Commutative _≡_ ∙) (assoc : Associative _≡_ ∙) (n : A) (ns : List A) → foldr ∙ ε (n ∷ ns) ≡ foldr ∙ (∙ n ε) ns
  notLemmaAux _∙_ ε comm assoc n [] = refl
  notLemmaAux _∙_ ε comm assoc n (m ∷ ns) = begin
    n ∙ (m ∙ foldr _∙_ ε ns) ≡˘⟨ assoc n m _ ⟩
    (n ∙ m) ∙ foldr _∙_ ε ns ≡⟨ cong (_∙ foldr _∙_ ε ns) (comm n m) ⟩
    (m ∙ n) ∙ foldr _∙_ ε ns ≡⟨ assoc m n _ ⟩
    m ∙ (n ∙ foldr _∙_ ε ns) ≡⟨ cong (m ∙_) (notLemmaAux _∙_ ε comm assoc n ns) ⟩
    m ∙ foldr _∙_ (n ∙ ε) ns ∎
    where
      open ≡-Reasoning

  foldr-downFrom-insert : ∀ {A : Set} (_∙_ : A → A → A) (ε : A) (f : ℕ → A) (n : ℕ) → foldr _∙_ (f zero ∙ ε) (applyDownFrom (λ x → f (suc x)) n) ≡ foldr _∙_ ε (applyDownFrom f (suc n))
  foldr-downFrom-insert _∙_ ε f zero = refl
  foldr-downFrom-insert _∙_ ε f (suc n) = cong (f (suc n) ∙_) (foldr-downFrom-insert _∙_ ε f n)

  notLemmaFilterAuxⁿ : ∀ {A : Set} (∙ : A → A → A) (ε : A) {p} {P : Pred A p} (P? : Decidable P) (f : ℕ → A) (n : ℕ) → ¬ P (f 0) → foldr ∙ ε (filter P? (applyDownFrom (λ x → f (suc x)) n)) ≡ foldr ∙ ε (filter P? (applyDownFrom f (suc n)))
  notLemmaFilterAuxⁿ ∙ ε P? f zero ¬p = cong (foldr ∙ ε) (sym (filter-reject P? ¬p))
  notLemmaFilterAuxⁿ ∙ ε P? f (suc n) ¬p with does (P? (f (suc n)))
  ... | false = notLemmaFilterAuxⁿ ∙ ε P? f n ¬p
  ... | true  = cong (∙ (f (suc n))) (notLemmaFilterAuxⁿ ∙ ε P? f n ¬p)

  foldr-filter-downFrom-insert : ∀ {A : Set} (_∙_ : A → A → A) (ε : A) {p} {P : Pred A p} (P? : Decidable P) (f : ℕ → A) (n : ℕ) → P (f zero) → foldr _∙_ (f zero ∙ ε) (filter P? (applyDownFrom (λ x → f (suc x)) n)) ≡ foldr _∙_ ε (filter P? (applyDownFrom f (suc n)))
  foldr-filter-downFrom-insert _∙_ ε P? f zero p = begin
    f zero ∙ ε ≡˘⟨ cong (foldr _∙_ ε) (filter-accept P? p) ⟩
    foldr _∙_ ε (filter P? (f zero ∷ [])) ∎
    where
      open ≡-Reasoning
  foldr-filter-downFrom-insert _∙_ ε P? f (suc n) p with does (P? (f (suc n)))
  ... | true = cong (f (suc n) ∙_) (foldr-filter-downFrom-insert _∙_ ε P? f n p)
  ... | false = foldr-filter-downFrom-insert _∙_ ε P? f n p

  notLemmaFilter : ∀ {A : Set} (∙ : A → A → A) (ε : A) (comm : Commutative _≡_ ∙) (assoc : Associative _≡_ ∙) {p} {P : Pred A p} (P? : Decidable P) (f : ℕ → A) (n : ℕ) → foldr ∙ ε (filter P? (applyUpTo f n)) ≡ foldr ∙ ε (filter P? (applyDownFrom f n))
  notLemmaFilter ∙ ε comm assoc P? f zero = refl
  notLemmaFilter ∙ ε comm assoc P? f (suc n) with P? (f zero)
  ... | false because ofⁿ ¬p = begin
    foldr ∙ ε (filter P? (applyUpTo (λ x → f (suc x)) n)) ≡⟨ notLemmaFilter ∙ ε comm assoc P? (λ x → f (suc x)) n ⟩
    foldr ∙ ε (filter P? (applyDownFrom (λ x → f (suc x)) n)) ≡⟨ notLemmaFilterAuxⁿ ∙ ε P? f n ¬p ⟩
    foldr ∙ ε (filter P? (applyDownFrom f (suc n))) ∎
    where
      open ≡-Reasoning
  ... | true because ofʸ p  = begin
    ∙ (f zero) (foldr ∙ ε (filter P? (applyUpTo (λ x → f (suc x)) n))) ≡⟨ notLemmaAux ∙ ε comm assoc (f zero) (filter P? (applyUpTo (λ x → f (suc x)) n)) ⟩
    foldr ∙ (∙ (f zero) (ε)) (filter P? (applyUpTo (λ x → f (suc x)) n)) ≡⟨ notLemmaFilter ∙ (∙ (f zero) ε) comm assoc P? (λ x → f (suc x)) n ⟩
    foldr ∙ (∙ (f zero) (ε)) (filter P? (applyDownFrom (λ x → f (suc x)) n)) ≡⟨ foldr-filter-downFrom-insert ∙ ε P? f n p ⟩
    foldr ∙ ε (filter P? (applyDownFrom f (suc n))) ∎
    where
      open ≡-Reasoning
  
  prop′ : ∀ d l → suc d * triangle″ (l / suc d) ≡ sum (filter (suc d ∣?_) (upTo (suc l)))
  prop′ d l = begin
    suc d * triangle″ (l / suc d)               ≡˘⟨ cong (λ x → suc d * x) (triangle≗triangle″ (l / suc d)) ⟩
    suc d * triangle (l / suc d)                ≡⟨ prop d l ⟩
    sum (filter (suc d ∣?_) (downFrom (suc l))) ≡˘⟨ notLemmaFilter _+_ 0 +-comm +-assoc (suc d ∣?_) (λ x → x) (suc l) ⟩
    sum (filter (suc d ∣?_) (upTo (suc l)))     ∎
    where
      open ≡-Reasoning

  recombine-divisors : ∀ d d′ xs → sum (filter (suc d ∣?_) xs) + sum (filter (suc d′ ∣?_) xs) ≡ sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs)
  recombine-divisors d d′ [] = refl
  recombine-divisors d d′ (x ∷ xs) with suc d ∣? x | suc d′ ∣? x
  ... | .true because ofʸ p | .true because ofʸ q = begin
    sum (filter (suc d ∣?_) (x ∷ xs)) + sum (filter (suc d′ ∣?_) (x ∷ xs)) ≡⟨ cong₂ (λ x y → sum x + sum y) (filter-accept (suc d ∣?_) p) (filter-accept (suc d′ ∣?_) q) ⟩
    sum (x ∷ filter (suc d ∣?_) xs) + sum (x ∷ filter (suc d′ ∣?_) xs) ≡⟨⟩
    (x + sum (filter (suc d ∣?_) xs)) + (x + sum (filter (suc d′ ∣?_) xs)) ≡⟨ +-assoc x (sum (filter (suc d ∣?_) xs)) _ ⟩
    x + (sum (filter (suc d ∣?_) xs) + (x + sum (filter (suc d′ ∣?_) xs))) ≡˘⟨ cong (x +_) (+-assoc (sum (filter (suc d ∣?_) xs)) x _) ⟩
    x + ((sum (filter (suc d ∣?_) xs) + x) + sum (filter (suc d′ ∣?_) xs)) ≡⟨ cong (λ n → x + (n + sum (filter (suc d′ ∣?_) xs))) (+-comm _ x) ⟩
    x + ((x + sum (filter (suc d ∣?_) xs)) + sum (filter (suc d′ ∣?_) xs)) ≡⟨ cong (x +_) (+-assoc x (sum (filter (suc d ∣?_) xs)) _) ⟩
    x + (x + (sum (filter (suc d ∣?_) xs) + sum (filter (suc d′ ∣?_) xs))) ≡˘⟨ +-assoc x x _ ⟩
    (x + x) + (sum (filter (suc d ∣?_) xs) + sum (filter (suc d′ ∣?_) xs)) ≡⟨ cong ((x + x) +_) (recombine-divisors d d′ xs) ⟩
    (x + x) + (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs)) ≡⟨ +-assoc x x _ ⟩
    x + (x + (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs))) ≡˘⟨ cong (x +_) (+-assoc x (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) _) ⟩
    x + ((x + sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs)) ≡⟨ cong (λ n → x + (n + sum (filter (lcm (suc d) (suc d′) ∣?_) xs))) (+-comm x _) ⟩
    x + ((sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + x) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs)) ≡⟨ cong (x +_) (+-assoc (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) x _) ⟩
    x + (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + (x + sum (filter (lcm (suc d) (suc d′) ∣?_) xs))) ≡˘⟨ +-assoc x (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) _ ⟩
    (x + sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) + (x + sum (filter (lcm (suc d) (suc d′) ∣?_) xs)) ≡⟨⟩
    sum (x ∷ filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + sum (x ∷ filter (lcm (suc d) (suc d′) ∣?_) xs) ≡˘⟨ cong₂ (λ x y → sum x + sum y) (filter-accept ((suc d ∣?_) ∪? (suc d′ ∣?_)) (inj₁ p)) (filter-accept (lcm (suc d) (suc d′) ∣?_) (lcm-least p q))⟩
    sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) (x ∷ xs)) + sum (filter (lcm (suc d) (suc d′) ∣?_) (x ∷ xs)) ∎
    where
      open ≡-Reasoning
  ... | .true because ofʸ p | .false because ofⁿ ¬q = begin
    sum (filter (suc d ∣?_) (x ∷ xs)) + sum (filter (suc d′ ∣?_) (x ∷ xs)) ≡⟨ cong₂ (λ x y → sum x + sum y) (filter-accept (suc d ∣?_) p) (filter-reject (suc d′ ∣?_) ¬q) ⟩
    sum (x ∷ filter (suc d ∣?_) xs) + sum (filter (suc d′ ∣?_) xs) ≡⟨ +-assoc x (sum (filter (suc d ∣?_) xs)) _ ⟩
    x + (sum (filter (suc d ∣?_) xs) + sum (filter (suc d′ ∣?_) xs)) ≡⟨ cong (x +_) (recombine-divisors d d′ xs) ⟩
    x + (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs)) ≡˘⟨ +-assoc x (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) _ ⟩
    (x + sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs) ≡˘⟨ cong₂ (λ x y → sum x + sum y) (filter-accept ((suc d ∣?_) ∪? (suc d′ ∣?_)) (inj₁ p)) (filter-reject (lcm (suc d) (suc d′) ∣?_) (λ r → ¬q (∣-trans (n∣lcm[m,n] (suc d) (suc d′)) r))) ⟩
    sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) (x ∷ xs)) + sum (filter (lcm (suc d) (suc d′) ∣?_) (x ∷ xs)) ∎
    where
      open ≡-Reasoning
  ... | .false because ofⁿ ¬p | .true because ofʸ q = begin
    sum (filter (suc d ∣?_) (x ∷ xs)) + sum (filter (suc d′ ∣?_) (x ∷ xs)) ≡⟨ cong₂ (λ x y → sum x + sum y) (filter-reject (suc d ∣?_) ¬p) (filter-accept (suc d′ ∣?_) q) ⟩
    sum (filter (suc d ∣?_) xs) + sum (x ∷ filter (suc d′ ∣?_) xs) ≡˘⟨ +-assoc (sum (filter (suc d ∣?_) xs)) x _ ⟩
    (sum (filter (suc d ∣?_) xs) + x) + sum (filter (suc d′ ∣?_) xs) ≡⟨ cong (_+ sum (filter (suc d′ ∣?_) xs)) (+-comm _ x) ⟩
    (x + sum (filter (suc d ∣?_) xs)) + sum (filter (suc d′ ∣?_) xs) ≡⟨ +-assoc x (sum (filter (suc d ∣?_) xs)) _ ⟩
    x + (sum (filter (suc d ∣?_) xs) + sum (filter (suc d′ ∣?_) xs)) ≡⟨ cong (x +_) (recombine-divisors d d′ xs) ⟩
    x + (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs)) ≡˘⟨ +-assoc x (sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) _ ⟩
    (x + sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs)) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs) ≡˘⟨ cong₂ (λ x y → sum x + sum y) (filter-accept ((suc d ∣?_) ∪? (suc d′ ∣?_)) (inj₂ q)) (filter-reject (lcm (suc d) (suc d′) ∣?_) λ r → ¬p (∣-trans (m∣lcm[m,n] (suc d) (suc d′)) r)) ⟩
    sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) (x ∷ xs)) + sum (filter (lcm (suc d) (suc d′) ∣?_) (x ∷ xs)) ∎
    where
      open ≡-Reasoning
  ... | .false because ofⁿ ¬p | .false because ofⁿ ¬q = begin
    sum (filter (suc d ∣?_) (x ∷ xs)) + sum (filter (suc d′ ∣?_) (x ∷ xs)) ≡⟨ cong₂ (λ x y → sum x + sum y) (filter-reject (suc d ∣?_) ¬p) (filter-reject (suc d′ ∣?_) ¬q) ⟩
    sum (filter (suc d ∣?_) xs) + sum (filter (suc d′ ∣?_) xs) ≡⟨ recombine-divisors d d′ xs ⟩
    sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) xs) + sum (filter (lcm (suc d) (suc d′) ∣?_) xs) ≡˘⟨ cong₂ (λ x y → sum x + sum y) (filter-reject ((suc d ∣?_) ∪? (suc d′ ∣?_)) [ ¬p , ¬q ]) (filter-reject (lcm (suc d) (suc d′) ∣?_) (λ r → ¬p (∣-trans (m∣lcm[m,n] (suc d) (suc d′)) r))) ⟩
    sum (filter ((suc d ∣?_) ∪? (suc d′ ∣?_)) (x ∷ xs)) + sum (filter (lcm (suc d) (suc d′) ∣?_) (x ∷ xs)) ∎
    where
      open ≡-Reasoning

solution′ : ℕ → ℕ
solution′ zero = zero
solution′ (suc n) = 3 * Lemmas.triangle″ (n / 3) + 5 * Lemmas.triangle″ (n / 5) ∸ 15 * Lemmas.triangle″ (n / 15)

solution-correct : problem′ ≗ solution′
solution-correct zero = refl
solution-correct (suc n) = begin
  sum (filter ((3 ∣?_) ∪? (5 ∣?_)) (upTo (suc n))) ≡˘⟨ +-identityʳ _ ⟩
  sum (filter ((3 ∣?_) ∪? (5 ∣?_)) (upTo (suc n))) + 0 ≡˘⟨ cong (sum (filter ((3 ∣?_) ∪? (5 ∣?_)) (upTo (suc n))) +_) (n∸n≡0 (sum (filter (15 ∣?_) (upTo (suc n))))) ⟩
  sum (filter ((3 ∣?_) ∪? (5 ∣?_)) (upTo (suc n))) + (sum (filter (15 ∣?_) (upTo (suc n))) ∸ sum (filter (15 ∣?_) (upTo (suc n)))) ≡˘⟨ +-∸-assoc (sum (filter ((3 ∣?_) ∪? (5 ∣?_)) (upTo (suc n)))) {sum (filter (15 ∣?_) (upTo (suc n)))} ≤-refl ⟩
  (sum (filter ((3 ∣?_) ∪? (5 ∣?_)) (upTo (suc n))) + sum (filter (15 ∣?_) (upTo (suc n)))) ∸ sum (filter (15 ∣?_) (upTo (suc n))) ≡˘⟨ cong (_∸ sum (filter (15 ∣?_) (upTo (suc n)))) (Lemmas.recombine-divisors 2 4 (upTo (suc n))) ⟩
  (sum (filter (3 ∣?_) (upTo (suc n))) + sum (filter (5 ∣?_) (upTo (suc n)))) ∸ sum (filter (15 ∣?_) (upTo (suc n))) ≡˘⟨ congₙ 3 (λ x y z → x + y ∸ z) (Lemmas.prop′ 2 n) (Lemmas.prop′ 4 n) (Lemmas.prop′ 14 n) ⟩
  (3 * Lemmas.triangle″ (n / 3) + 5 * Lemmas.triangle″ (n / 5)) ∸ 15 * Lemmas.triangle″ (n / 15) ∎
  where
    open ≡-Reasoning

solution : ℕ
solution = solution′ 1000

-- output the solution
open import Data.Nat.Show
open import IO
import IO.Primitive as Prim

main : Prim.IO _
main = run (putStrLn (show solution))
