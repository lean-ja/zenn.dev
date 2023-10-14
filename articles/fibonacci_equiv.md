---
title: "フィボナッチ数列の2通りの定義が等しいことを，Lean4: Theorem Prover を使って証明する"
emoji: "🐦"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系", "数学"]
published: true
---

Lean に関する小ネタを紹介します．テーマはフィボナッチ数列を計算する2通りのアルゴリズムが等しいことの検証です．フィボナッチ数列を定義通りに素朴に実装すると非常に非効率になるのは有名な話ですが，その高速化が元の定義と同値であることの証明はきちんとされたことがないのではないでしょうか？

Zenn では Lean のシンタックスハイライトが効かなくてコード例を共有するのが手間なので，gist をそのまま貼ってしまいます．

@[gist](https://gist.github.com/Seasawher/33cab5255dc5d5febab7d879e9b4fa34)

[Lean4 web](https://t.ly/tmjm3) のリンクも貼っておきます．