---
title: "Lean Prover コマンド紹介"
emoji: "☄️"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系"]
published: true
---

Lean4 には `#` をつけて呼び出せるコマンドがいくつかあります．ほかの言語ではあまり見ない機能ですが，慣れれば大変便利ですので，ぜひ使い方を覚えていただきたいと思います．ここでは使用頻度が高いと思われるものに限ってご紹介しますが，全コマンドのリストが `#help command` で確認できますので，興味のある方はそちらも試してみてください．

`#eval`, `#check`, `#guard_msgs`, `#guard`, `#print`, `#find` の6コマンドを紹介します．

今回のコードも [Lean web editor](https://live.lean-lang.org/) で実際に試すことができます．コピーして試してみてください．

@[gist](https://gist.github.com/Seasawher/d3ab5bbe9ba2ab3a70fe2440ec65b149)