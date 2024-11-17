---
title: "Lean で数学的帰納法を末尾再帰で実装する"
emoji: "🙃"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系", "数学", "再帰", "帰納法"]
published: true
---

著者：[s-taiga](https://github.com/s-taiga)
これは[証明支援系 Advent Calendar 2024](https://adventar.org/calendars/10209)の14日目の記事です。

# 概要

自然数とリストについての数学的帰納法を末尾再帰になるように実装してみます。
本記事では特に Lean についての解説を挟まないで書いていきますので、Lean 初めましての方は lean-ja の各種ドキュメントをご活用くださいませ。（宣伝）

なお、タイトルを見て Lean での証明の irrelevance をご存じの方はそっとマサカリを構えられるかもしれませんが、どうか最後までお付き合いいただけますと幸いです。

# 再帰関数と末尾再帰最適化

Lean を含め関数型言語で繰り返し処理を書くときは、たいてい帰納型に対する再帰になることが多いように思います。

```lean
def double : Nat → Nat
  | 0     => 0
  | n + 1 => double n + 2
```

しかし、再帰関数は繰り返しのたびにスタックが積まれるため、引数の値が大きいとスタックオーバーフローで処理が失敗してしまう危険性があります。
例えば上記の関数を[Lean 4 のwebエディタ](https://live.lean-lang.org/)に入れて `#eval` してみると10000くらいでもスタックオーバーフローで処理が停止してしまいます。

これを回避する方法の一つに末尾再帰という方法があります。
これは再帰関数内で最後に return する箇所で再帰関数を呼び出すようにするテクニックで、言語によってはこれによって再帰呼び出しがただのループに最適化されます。
Lean では末尾再帰最適化をサポートしているため、上記の関数を末尾再帰にした下記の関数は大きな自然数を与えてもちゃんと答えが返ります。

```lean
def doubleTail(n : Nat) : Nat := aux n 0
  where
  aux : Nat → Nat → Nat
  | 0,     acc => acc
  | n + 1, acc => aux n (acc + 2)
```

末尾再帰最適化は上記のように補助関数を作り、補助関数では計算結果を貯めていく用の引数（以下アキュムレータと呼びます）を追加することが多いです。
このスタイルは [accumulator passing style](https://lean-ja.github.io/fp-lean-ja/programs-proofs/tail-recursion.html) とも言われます。

# 数学的帰納法

さて、この再帰関数によって数学的帰納法を書くことができます。
まず上記の `double` 関数の性質を Lean で素直に証明すると以下のようになります。

```lean
theorem proveDouble : ∀ n, double n = 2 * n := by
  intro n
  induction n with
  | zero     => simp [double]
  | succ n h => unfold double; rw [h, Nat.mul_add]
```

`induction` のあたりが数学的帰納法ですが、この部分をパターンマッチに、帰納法の仮定を再帰呼び出しにそれぞれ置き換えることが可能です。

```lean
theorem proveDoubleRec : ∀ n, double n = 2 * n
  | 0     => by simp [double]
  | n + 1 => by unfold double; rw [proveDoubleRec n, Nat.mul_add]
```

ところで、前節を踏まえるとこの関数は末尾再帰ではないのがわかるでしょうか？
これは数学的帰納法のロジックだけを抜き出した関数を再帰関数で書いてみるとよりはっきりします。

```lean
theorem recInduction
  (P : Nat → Prop)
  (bc : P 0) (ih : (k : Nat) → P k → P (k + 1))
  : ∀ N, P N
    | 0     => bc
    | n + 1 => ih n <| recInduction P bc ih n
```

ということは、これも先ほどのやり方を踏襲すれば末尾再帰にすることができそうです！

素直にマネするなら以下のようになるでしょう。
先ほどと違う点として、アキュムレータと戻り値の型が単純な型ではなく、自然数の値に依存した型だというところです。

```lean
theorem tailRecInduction
  (P : Nat → Prop)
  (bc : P 0) (ih : (k : Nat) → P k → P (k + 1))
  (N : Nat) : P N :=
    aux N bc
    where
      aux : (n : Nat) → P ? → P ?
      | 0,     acc => acc
      | n + 1, acc => aux n (by ... acc を使った証明 ...)
```

この `?` には何が入るでしょうか？
普通の数学的帰納法ではパターンマッチの分岐は、`0` のケースでは `P 0` を、`n + 1` のケースでは `P (n + 1)` の値をそれぞれ返すので、それに合わせてみます。
すると `aux : (n : Nat) → P n → P n` となりますが、これだと見ての通りアキュムレータをそのまま返せばよい関数になってしまい明らかに変です。

したがって、末尾再帰の場合は普通の再帰と違い、パターンマッチする変数と戻り値（ついでにアキュムレータ）に依存する値がそのまま結びつかないのです。
では実際それぞれどの自然数の値に紐づいているのか `doubleTail` の補助関数を観察してみましょう。

# 末尾再帰の挙動

例として `aux 5 0` を手で `eval` してみます。
まずこの時点で、アキュムレータの値は基本ケースの値である `0` に依存していることがわかります。
したがってここでの `acc` の型は疑似的な表現ですが `Nat 0` のようなものになるはずです。
また、戻り値はそのまま `doubleTail` の結果になるので `Nat 5` のような感じのはずです。

では1つステップを進めてみましょう。

```
aux 5 0
=> aux 4 (0 + 2)
```

アキュムレータは基本ケースに `double` を1つ進めた値になっているため、`Nat 1` です。
そして戻り値はやはり `doubleTail` の結果になるので `Nat 5` です。

もう1つ進めます。

```
aux 4 (0 + 2)
=> aux 3 ((0 + 2) + 2)
```

アキュムレータは前回の値をさらに `double` したものになっているので `Nat 2` です。
戻り値については言わずもがな `Nat 5` です。

ここまでの観察からわかる通りパターンマッチする数が呼び出しのたびに1ずつ減る一方で、アキュムレータは `0` から**1ずつ増えていき**、戻り値の型は**ずっと変わらないまま**になります。
したがって、`doubleTail N` で呼び出された時に `aux` でパターンマッチする数が `n` の時、アキュムレータは `N - n` に、戻り値は `N` に依存した値になっているのです。
よって `tailRecInduction` の `aux` の型は `aux : (n : Nat) → P (N - n) → P N` という感じになります。

# 実装

さて、実装するにあたりパターンマッチした時の状況を具体的に考えてみましょう。
まず `n` が `0` の場合、アキュムレータの型は `P (N - 0)` であるため、戻り値の型が `P N` であることからアキュムレータをそのまま返せばよいことがわかります。
この挙動はまさに `doubleTail` の `aux` における `0` のケースと同じですね！

次に `n` が `k + 1` の場合、アキュムレータの型は `P (N - (k + 1))` となります。
ここで目的の `P N` は `aux` に `k` と、その時のアキュムレータ `P (N - k)` を適用すれば得られるため、あとはこの `P (N - k)` の項を作ればよいわけです。

もともとのアキュムレータの型が依存している値 `N - k - 1`（展開しています）とアキュムレータを帰納法の仮定 `ih : (k : Nat) → P k → P (k + 1)` に適用すると、`P (N - k - 1 + 1)` が得られます。
この型の足し引きを計算すると`P (N - k)`になるのでこれでいけそうですが、この計算結果が成り立つには`N - k - 1`が整数として計算した時に負にならないことが必要です。
したがって `k + 1 ≤ N` という条件が必要になるので、`aux` としては `n ≤ N` を追加してあげれば証明が完了することになります！

以上をまとめて、必要な証明を入れ込むと以下のような実装になります。

```lean
theorem tailRecInduction
  (P : Nat → Prop)
  (bc : P 0) (ih : (k : Nat) → P k → P (k + 1))
  (N : Nat) : P N :=
    aux N N.le_refl (N.sub_self ▸ bc)
    where
      aux : (n : Nat) → n ≤ N → P (N - n) → P N
      | 0,     _, PN'  => PN'
      | k + 1, h, PNk1 => aux k (Nat.le_trans (k.le_add_right 1) h) (by
        rw [Nat.sub_add_eq] at PNk1
        have := ih (N - k - 1) PNk1
        suffices h' : 1 ≤ N - k from by
          exact Nat.sub_add_cancel h' ▸ this
        rw [← Nat.add_sub_cancel 1 k]
        apply Nat.sub_le_sub_right
        exact Nat.add_comm 1 k ▸ h
      )
```

`1 ≤ N - k` のための証明で少し幅を取っていますが、`n + 1` のケースでちゃんと `aux` を末尾再帰呼び出しできていることがわかります！
また補助関数の引数のアキュムレータと戻り値の型が依存型になったことにより、accumulator passing style の処理がどういう性質のものであるかがよりはっきりしたと思います。

## `N - n` の値を明示したバージョン

上記は accumulator passing style になるべく忠実に実装したものになりますが、`N - n` の値を明示的にするように `aux` を書き換えると証明がちょっと短くなります。

```lean
theorem tailRecInduction'
  (P : Nat → Prop)
  (bc : P 0) (ih : (k : Nat) → P k → P (k + 1))
  (N : Nat) : P N :=
    aux N ⟨0, by simp, bc⟩
    where
      aux : (n : Nat) → (∃ m : Nat, n + m = N ∧ P m) → P N
      | 0,     ⟨N', hN', PN'⟩ => by
        simp at hN'
        exact hN' ▸ PN'
      | k + 1, ⟨m, hm, Pm⟩ => aux k (by
        exists 1 + m
        constructor
        . exact Nat.add_assoc k 1 m ▸ hm
        exact Nat.add_comm 1 m ▸ ih m Pm
      )
```

不等式を使ってないため証明も平易でいい感じです。

# リストに対する帰納法

実は上記の性質はリストに対する帰納法を末尾再帰化するとさらにはっきりします。
まず普通の再帰バージョンは以下の感じです。

```lean
theorem listInduction
  {A} (P : List A → Prop)
  (bc : P []) (ih : ∀ (a : A)(as : List A), P as → P (a :: as))
  : ∀ L: List A, P L
    | [] => bc
    | a :: as => ih a as <| listInduction P bc ih as
```

ほぼ自然数の帰納法と同じですね！

じゃあ末尾再帰版もやってみましょう。
1つ目の証明では `N - n` という性質を用いていますが、リストで引き算はだいぶ難しいので、2つ目の証明の方針を取ることにします。

```lean
theorem tailRecListInduction
  {A} (P : List A → Prop)
  (bc : P []) (ih : ∀ (a : A)(as : List A), P as → P (a :: as))
  (L : List A) : P L :=
    aux L ⟨[], by simp, bc⟩
    where
      aux : (ls : List A) → (∃ ms : List A, ls ++ ms = L ∧ P ms) → P L
      | [],      ⟨L', hL', PL'⟩ => by
        simp at hL'
        exact hL' ▸ PL'
      | l :: ls, ⟨ms, hms, Pms⟩ => aux ls (by
        _
        -- hms : l :: ls ++ ms = L
        -- Pms : P ms
        -- ⊢ ∃ ms, ls ++ ms = L ∧ P ms
        -- exists l :: ms して ih l ms Pms ?
      )
```

`[]` のケースは自然数の場合と同じようにいけます。
ところが `l :: ls` のケースでは破綻してしまいます。
自然数と同じ路線をたどるならコメントに書いたように `l :: ms` をベースに証明していきますが、その場合証明することになるのは `ls ++ l :: ms = L ∧ P (l :: ms)` ですが、左の式が完全に `hms` と矛盾しちゃっています。
つまり、この `aux` の型ではダメなわけです。

問題なのは `ls` のパターンマッチで先頭から見ていくところなので、イメージ的には `ls ++ [l]` という感じでパターンマッチできれば証明が通ってくれそうです。
つまり引数のリストを reverse したものに末尾再帰していけばいいわけです。
なので実は自然数の場合は足し算が可換であることで問題なかっただけで、本当は同じように概念上反対向きにパターンマッチするのが正しかったわけです。
これを踏まえて実装すると以下のようになります。

```lean
theorem tailRecListInduction
  {A} (P : List A → Prop)
  (bc : P []) (ih : ∀ (a : A)(as : List A), P as → P (a :: as))
  (L : List A) : P L :=
    aux L.reverse ⟨[], by simp, bc⟩
    where
      aux : (revFront : List A) → (∃ back : List A, revFront.reverse ++ back = L ∧ P back) → P L
      | [], ⟨L', hL', PL'⟩ => by
        simp at hL'
        exact hL' ▸ PL'
      | mid :: revFront, ⟨back, hback, Pback⟩ => aux revFront (by
        exists mid :: back
        constructor
        . rw [List.append_cons, ← List.reverse_cons]
          exact hback
        exact ih mid back Pback
      )
```

というわけで末尾再帰というものは

- 再帰対象を逆向きにパターンマッチして
- 示したい値の残りを埋めるように値を蓄積して
- 補助関数の戻り値としては一貫してもとの再帰関数の戻り値と同じである

ようにしたものであることがわかりました！

# ちなみに

Lean において `Prop` に属する対象は [irrelevance](https://lean-ja.github.io/reference-manual-ja/Lean-_____________________The-Lean-Language___/__________________The-Type-System___/#The-Lean-Language-Reference-____________--Lean-_____________________The-Lean-Language___--__________________The-Type-System___--_________--_____________________--Relevance) と言ってコンパイル時にはきれいさっぱり消去されます。
したがって本記事で作った定理は**まるっきり無駄です**。
（ただ、自然数の1つ目のバージョンは存在量化子を使ってないので、`P` の型を `Nat → Type u` にすることができるため、依存型の末尾再帰関数に応用することが可能です。）
