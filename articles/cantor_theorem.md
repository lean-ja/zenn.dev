---
title: "Lean 4 でカントールの定理"
emoji: "🤙"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系", "数学"]
published: true
---

Lean 4 を使ってカントールの定理（ある集合からそのベキ集合への全射は存在しない）を示します．

コード片をコメント付きで載せます．

```haskell
import Mathlib.Tactic.Common

universe u

variable (X : Type u)
open Function

example (f : X → Set X) : ¬ Surjective f := by
  -- f が全射だと仮定する
  intro (hsurj : Surjective f)

  -- X の部分集合 Y を， 以下のように取る
  -- Y = {x | x ∉ f(x)}
  let Y := {x | x ∉ f x}

  -- f は全射なので， f x = Y となる x が存在する
  obtain ⟨x, hx⟩ := hsurj Y

  -- x について， x ∈ Y ↔ x ∉ Y が示せる
  have : x ∈ Y ↔ x ∉ Y := by
    constructor

    -- 左から右を示す
    case mp =>
      -- x ∈ Y だと仮定する
      intro hY

      -- Y の定義から， x ∉ f x
      replace hY : x ∉ f x := by aesop

      -- f x = Y だったから， x ∉ Y
      rwa [hx] at hY

    -- 右から左を示す
    case mpr =>
      -- x ∉ Y だと仮定する
      intro hY

      -- f x = Y だったから， x ∉ f x
      replace hY : x ∉ f x := by rwa [← hx] at hY

      -- Y の定義から， x ∈ Y
      assumption

  -- これは矛盾である．
  tauto
```