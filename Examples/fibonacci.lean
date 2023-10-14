import Mathlib.Tactic

/-- フィボナッチ数列の通常の定義をそのまま Lean の関数として書いたもの -/
def fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fibonacci n + fibonacci (n + 1)

-- 最初の数個の値に対してテストする
example : [0, 1, 2, 3, 4, 5].map fibonacci = [0, 1, 1, 2, 3, 5] := by rfl

/-- フィボナッチ数列の速いバージョン -/
def fib (n : Nat) : Nat :=
  (loop n).1
where
  -- ヘルパー関数を定義する
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)

-- 最初の数個の値に対してテストする
-- `fibonacci` と同じ値になっている様子
example : [0, 1, 2, 3, 4, 5].map fib = [0, 1, 1, 2, 3, 5] := by rfl

/-- `fib` が `fibonacci` と同じ漸化式を満たすことを証明する -/
theorem fib_add (n : Nat) : fib n + fib (n + 1) = fib (n + 2) := by

  -- ヘルパー関数について示せば十分
  suffices fib.loop n + fib.loop (n + 1) = fib.loop (n + 2) from by rfl

  -- 定義をもとに計算すれば示せる
  rfl

/-- `fibonacci` と `fib` は同じ結果を返す -/
example : fibonacci = fib := by
  -- 関数が等しいことを示すので，引数 `n` が与えられたとする
  funext n

  -- `n` についての強い帰納法で示す
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp_all [←fib_add, fibonacci]