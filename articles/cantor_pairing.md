---
title: "Lean Prover で Cantor の対関数に逆写像があることを示す"
emoji: "🥐"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系", "数学", "集合論"]
published: true
---

## はじめに

Lean 4 は, 純粋関数型プログラミング言語のひとつです．依存型と呼ばれる表現力の高い型システムを持ち，正しいコードを容易に書くことができるように設計されています．Lean は，さらに証明支援系としても使うことができます．世界で数学コミュニティを中心に広まりつつあり，数学界隈で今最もアツいプログラミング言語であると言っても過言ではありません．

mathlib という Lean で数学理論を実装した大きなライブラリがあり，今回はそれを利用して証明を行います．

Cantor の対関数とは，`ℕ × ℕ` から `ℕ` へのある全単射関数のことです．後でコード例の中で定義をします．

## コード例

コメント付きで単にコードを載せます．わからないタクティクがあれば，[タクティク逆引きリスト](https://lean-ja.github.io/tactic-cheatsheet/)などを参照してください．

@[gist](https://gist.github.com/Seasawher/3fc8e3055d3f5997bdf48282355ff1ac)