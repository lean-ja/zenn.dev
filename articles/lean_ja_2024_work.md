---
title: "lean-jaのドキュメント紹介"
emoji: "✍"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系"]
published: true
---

著者：[s-taiga](https://github.com/s-taiga)
これは[証明支援系 Advent Calendar 2024](https://adventar.org/calendars/10209)の 16 日目の記事です。

本稿では lean-ja が公開しているドキュメントを紹介したいと思います。
その前に簡単に lean-ja について説明させていただきます。

## lean-ja について

https://github.com/lean-ja

lean-ja は Lean に関する情報の交換と集積を目的としたコミュニティです。
Lean、特に Lean 4 はリリースされてからようやく 1 年くらいであるため、知名度および日本語の文献が非常に少ない状況です。
そこで本コミュニティでは Lean についての日本語文献の充実を一つの目標に据えています。

以下が lean-ja でホストしている文献です。
現在は 1 つを除いて英語ドキュメントの翻訳が主な状況です。

# Lean by Example

https://lean-ja.github.io/lean-by-example/

Lean を記述する上で必要なコマンド・タクティク・オプション・属性などを幅広く、まとめ・解説された資料です。
Lean 4 についての日本語による唯一の包括的な一次文献でありかなり貴重な存在です。
また更新頻度も非常に高いため最新の機能の解説もすぐに取り込まれている点も非常にありがたいです。
ある程度 Lean に慣れたらかなり役立つ書籍です！

# Theorem Proving in Lean 4

https://aconite-ac.github.io/theorem_proving_in_lean4_ja/

Lean による定理証明機能の体系的なチュートリアル本の和訳です。原文は[こちら](https://lean-lang.org/theorem_proving_in_lean4/)です。
依存型理論から始まり Lean の各種機能を紹介しながら証明の仕方を紹介しているドキュメントです。
Lean 初学者がまず読むとしたら Lean 本文についている[マニュアル](https://lean-lang.org/lean4/doc/)か、本書から読むべきと言っても良いくらい優れた導入本だと思います。

# Functional Programming in Lean

https://lean-ja.github.io/lean-by-example/

Lean による関数型プログラミングのチュートリアル本の和訳です。原文は[こちら](https://lean-ja.github.io/lean-by-example/)です。
内容の難易度は私の体感的には[すごい H 本](https://www.ohmsha.co.jp/book/9784274068850/)より若干難し目ですが、関数型プログラミングの基本から依存型・証明を絡めたコーディングまで数多くの具体例を備えた良書です。
ただし、本書は 3 章以降は私のセルフチェックだけで公開していることもあり訳が不正確な可能性が非常に高いです……

# Mathematics in Lean

https://lean-ja.github.io/mathematics_in_lean_source/

Lean による数学の形式化のチュートリアル本の和訳です。原文は[こちら](https://leanprover-community.github.io/mathematics_in_lean/index.html)です。
Lean での数学的証明の基本から Mathlib の使い方を通じて大学数学の形式化のノウハウを幅広くまとめた本です。
冒頭で数学知識はあまり要らないみたいなことが書かれていますが、大学で数学を学んでこなかった身としては正直かなり難しかったです。
数学的証明の練習という意味では英語ですが[The Mechanics of Proof](https://hrmacbeth.github.io/math2001/index.html)の方が入りやすいかもしれないです。
ただし、本書も 3 章以降は私のセルフチェックだけで公開していることもあり訳が不正確な可能性が非常に高いです……

# Metaprogramming in Lean 4

https://lean-ja.github.io/lean4-metaprogramming-book-ja/

Lean 4 でのメタプログラミングのチュートリアル本の和訳です。原文は[こちら](https://leanprover-community.github.io/lean4-metaprogramming-book/)です。
ただし、本書は全編私のセルフチェックだけで（ry

# Type Checking in Lean 4

https://lean-ja.github.io/type_checking_in_lean4_ja/

Lean 4 のカーネルおよび型チェックの機構についてのドキュメントの和訳です。原文は[こちら](https://ammkrn.github.io/type_checking_in_lean4/)です。
型理論やラムダ計算などをあらかじめ知っていないと難しそうな内容でした。
こちらも私のセルフチェックだけで公開しています。

# The Lean Language Reference

https://lean-ja.github.io/reference-manual-ja/

Lean の言語リファレンスです。原文は[こちら](https://lean-lang.org/doc/reference/latest/)です。
こちらは現在進行形で執筆されている文献になりまして、随時変更を翻訳して反映しています。
ちなみに本書は[Verso](https://github.com/leanprover/verso)という Lean 製のドキュメント生成ツールを用いており、コード例で項の型やドキュメントコメントが見れてかなり読みやすいところもおすすめです。
