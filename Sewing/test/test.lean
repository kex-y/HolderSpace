import mathlib

/-
If $a$ and $r$ are real numbers and $r \neq 1$, then
$$
\sum_{j=0}^{n} a r^{j}=a+a r+a r^{2}+\cdots+a r^{n}=\frac{a r^{n+1}-a}{r-1}.
$$
-/

open Finset

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) :
    ∑ i ∈ range (n + 1), a * r^i = (a * r^(n + 1) - a) / (r - 1) := by
  have hr := fun h' => h <| sub_eq_zero.1 h'
  induction' n with n ih
  · simp only [zero_add, range_one, sum_singleton, pow_zero, mul_one, pow_one]
    rw [eq_div_iff_mul_eq hr, mul_sub, mul_one]
  · rw [sum_range_succ, ih, eq_div_iff_mul_eq hr, add_mul,
      div_mul_cancel₀ _ hr, pow_succ _ (n + 1)]
    ring

/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

example {n k : ℕ} (h : k ≤ n) :
    n.choose 0 = 1 ∧ n.choose n = 1 ∧ n.choose k = n.choose (n - k) :=
  ⟨n.choose_zero_right, n.choose_self, (Nat.choose_symm h).symm⟩

/-
We define a function recursively for all positive integers $n$ by $f(1)=1$,
$f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$. Show that $f(n)= 2^{n}+(-1)^{n}$,
using the second principle of mathematical induction.
-/

def f : ℕ → ℕ
  | 0 => 0 -- Junk value for the zero case
  | 1 => 1
  | 2 => 5
  | n + 2 => f (n + 1) + 2 * f n -- Replaced n by n + 1

lemma f_succ {n : ℕ} (hn₀ : n ≠ 0) :
    f (n + 2) = f (n + 1) + 2 * f n := by
  rwa [f]

example {n : ℕ} (hn : 0 < n) : (f n : ℤ) = 2^n + (-1)^n := by
  induction' n using Nat.twoStepInduction with n ih ih'
  · norm_num at hn
  · simp [f]
  · by_cases hn₀ : n = 0
    · simp [hn₀, f]
    rw [f_succ hn₀]
    push_cast
    rw [ih (Nat.zero_lt_of_ne_zero hn₀), ih' n.zero_lt_succ, mul_add, pow_add, pow_add, pow_add]
    ring
