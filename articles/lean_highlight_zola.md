---
title: "静的サイトジェネレータ(SSG)で作成したサイトにおいて， Lean4 のシンタックスハイライトを効かせる方法"
emoji: "🎇"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系", "SSG"]
published: true
---

Lean4 はまだまだ新しい言語なので， シンタックスハイライトが効かなくて困るということがよく発生します． GitHub や Lean 公式 Zulip ではハイライトが効きますが， はてなブログやここ Zenn ではハイライトが効きません．

ブログサービスを利用する場合はシンタックスハイライトが効かないことに対して待つ以外にできることがありませんが， SSG(静的サイトジェネレータ)で手作りすればある程度自力で修正することができます．

## 方法1: Pygments を使う

[Pygments](https://pygments.org/) は Lean に対応していますので， Pygments が使える SSG を使用すれば， シンタックスハイライトを効かせることが可能です．

例えば [Nikola](https://getnikola.com/) は Pygments に対応しており， [Lean Prover Community の公式ブログ](https://leanprover-community.github.io/blog/) で使用されていたりします．

## 方法2: 既存の `highlight.js` を使用する

SSG として mdbook を使用している場合は，既存の `highlight.js` ファイルをコピーして適切な場所に配置し，設定を調整することで解決することができます．

https://github.com/leanprover/lean4/blob/master/doc/highlight.js

## 方法3: 既存の `lean4.json` を使用する

Lean の VSCode 拡張では， 次のファイルで構文を定義しています．

https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/syntaxes/lean4.json

これを元に自前でシンタックスハイライトを実装することができます．

例えば Rust 製の SSG である [Zola](https://www.getzola.org/) の場合， デフォルトでは Lean のシンタックスハイライトが効きませんが， `*.sublime-syntax` ファイルを追加すれば効かせることができます．Zola は `.json` ファイルによるシンタックスハイライトは受け付けていないため，なんらかの方法で同等な `*.sublime-syntax` ファイルを用意する必要がありますが，それを(手動で)行ったものがこちらにあります．

https://github.com/lean-ja/lean-sublime-syntax/blob/main/lean.sublime-syntax

上記のファイルを [Zola のドキュメント](https://www.getzola.org/documentation/content/syntax-highlighting/)を参考に配置して，設定を調整すればハイライトが効くようになります．

なお lean-ja での目的のために手動で調整したものなので，上記の公式の構文とは少し異なるところがあります．