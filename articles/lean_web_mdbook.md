---
title: "mdbook に Lean4 のコードブロックを Playground で実行するボタンを追加する"
emoji: "🏄"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系", "mdbook"]
published: true
---

## はじめに

mdbook は，markdown を書くだけで自動で HTML, CSS, JavaScript を生成してオシャレなドキュメントを作成することができてしまう，すっごく便利な静的サイトジェネレータです．

https://github.com/rust-lang/mdBook

Rust 製であり，Rust 関連のツールのドキュメントによく使われています．しかし，Rust と関係がないドキュメントでも便利です．私自身は lean prover 関連のドキュメントの作成などに使用しています．

ところで mdbook には Playground といって，コードブロックに「実行」ボタンを追加し，それをクリックするだけで実行できるという機能もあります．しかし，それは Rust のコードに対してだけであって，他の言語，たとえば lean prover のコードブロックに対しては使うことができません．

でも，ドキュメントに書いてあるコードをすぐに実行出来たらきっと便利ですよね？

今回は，mdbook をカスタマイズすることにより，lean のコードブロックに対して実行ボタンを追加する方法をご説明します．

## 実装

### 方針

さて，上記では「実行ボタンを追加する」と言いましたが，ここでいう「実行」とは「コードが rust の online playground 経由で実行されて，出力がコードブロックの下にテキストとして表示される」という一連の流れのことです．

Rust ならこれで良いのですが，冷静に考えてみると lean prover に対してはそれでは不十分です．証明の間に goal と local context がどのように変化するのか自分で確かめてみたいというニーズが大きいだろうと考えられるからです．つまり，「実行ボタン」ではなくて，「lean がブラウザ上で実行できる環境へと連れていってくれるボタン」が必要です．幸いなことに lean playground は既にありますので，これを利用する方法を考えることになります．

https://live.lean-lang.org/

### URL の加工

上記の lean playground はよくできていて，コードを貼った状態での URL をコピーして貼り付けると，同じコードが貼られた状態を再現することができます．つまり，URL でコード共有ができます．

具体的には，lean playground 自体の URL が `https://live.lean-lang.org/` なのですが，コードを書き始めるとエスケープされてこれが `https://live.lean-lang.org/#code={hogehoge}` に変化します．この `{hogehoge}` の部分をコードから計算することができれば，特定のコードがすでに貼られた状態の playground へ飛ぶリンクが作れます．

そしてこの `{hogehoge}` へのエスケープの実装方法ですが，JavaScript の `encodeURIComponent` 関数を呼んでいるだけであることが判明しました．これはもちろん容易に再現できます．

### mdbook にボタンを追加する

次に，mdbook にボタンを実際に追加する必要があります．既存の「コードをコピーするボタン」等がどのように実装されているかといえば，`book.js` というファイルがありそこにコードが書かれています．これを真似するのが楽だと思います．

mdbook はカスタマイズ性が優れていて，設定ファイルの `additional-js` という項目を設定することでカスタムJSを読み込むことができます．これを利用して JavaScript コードを追加しましょう．

https://rust-lang.github.io/mdBook/format/configuration/renderers.html#html-renderer-options

実際の JavaScript の実装ですが，以下のコードで OK だと思います．

https://github.com/lean-ja/tactic-cheetsheet/blob/main/assets/leanweb.js

上記のコードをコピペするなりなんなりして配置すれば，もう実装完了です．お疲れさまでした．mdbook の拡張性の高さと，既に lean playground が用意されているおかげで簡単でしたね．

## 最後に

上記のようにして playground に飛ぶボタンを追加したものがこちらです．

https://lean-ja.github.io/tactic-cheetsheet/

「 playground に飛ぶボタンが実装される」ことを想定して作ったわけではないため，あまり望ましくない挙動になっている箇所がありますが，最初からこの挙動を理解した上で作れば，便利なボタンだと感じてもらえると期待しています．

これをきっかけに，もっと lean に関するドキュメントが盛んに制作されたらいいなと思います．
