---
title: "Lean4 で print デバッグをする"
emoji: "🩺"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系", "デバッグ"]
published: true
---

プログラムにバグがあったとき，関数の途中で変数に何が入っているのか確かめたくなるのが人情というものです．

Python だったら `print` 関数を使うところですが，Lean Prover でそれをするには `dbg_trace` というコマンドが用意されています．

試しに Fibonacci 数列の指数時間と線形時間の実装に対して，それぞれ `n` での値を計算するのに再帰呼び出しがどのように行われているのか見てみましょう．

@[gist](https://gist.github.com/Seasawher/5c109371ec5661d270f7909761a3b10f)
