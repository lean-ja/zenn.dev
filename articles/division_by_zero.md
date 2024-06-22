---
title: "Division by zero in type theory: a FAQ 日本語訳"
emoji: "📑"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系", "xena日本語訳"]
published: true
---

:::message
これは [Xena](https://xenaproject.wordpress.com/) の記事の有志による非公式翻訳です．
原文は [Division by zero in type theory: a FAQ](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/) です．
翻訳に際して，機械翻訳サービス[DeepL翻訳](https://www.deepl.com/ja/translator)を参考にしました．
:::

<!-- ## Hey! I heard that Lean thinks 1/0 = 0. Is that true? -->
## ねえ, Lean では 1/0＝0 だって聞いたんだけど, 本当？

<!-- Yes. So do Coq and Agda and many other theorem provers. -->

本当ですよ．Coq や Agda，その他多くの証明支援系と同じです．

<!-- ## Doesn’t that lead to contradictions? -->
## それは矛盾にならないの？

<!-- No. It just means that Lean’s $/$ symbol doesn’t mean mathematical division. Let $\mathbb{R}$ denote the real numbers. Let’s define a function $f:\mathbb{R}^2\to\mathbb{R}$ by $f(x,y)=x/y$ if $y\not=0$ and $f(x,0)=0$. Does making that definition give us a contradiction in mathematics? No, of course not! It’s just a definition. Lean uses the symbol $/$ to mean $f$. As does Coq, Agda etc. Lean calls it `real.div` by the way, not $f$. -->

いいえ．Lean の $/$ 記号が数学的な割り算を意味しないというだけです．$\mathbb{R}$ を実数全体とします．関数 $f:\mathbb{R}^2\to\mathbb{R}$ を  $y\not=0$ に対しては $f(x,y)=x/y$ であり，$y=0$ のとき $f(x,0)=0$ を満たすようなものとして定義します．この定義が数学に矛盾をもたらすでしょうか？もちろんそんなことはありません！単なる定義です．Lean は $/$ 記号を $f$ の意味で使います．Coq や Agda と同じようにです．この関数は Lean では実際には $f$ ではなく，`real.div` と呼ばれます．

<!-- ## But doesn’t that lead to confusion? -->
## でも，混乱しない？

<!-- It certainly seems to lead to confusion on Twitter. But it doesn’t lead to confusion when doing mathematics in a theorem prover. **Mathematicians don’t divide by 0** and hence in practice they never notice the difference between `real.div` and mathematical division (for which `1/0` is undefined). Indeed, if a mathematician is asking what Lean thinks `1/0` is, one might ask the mathematician why they are even asking, because as we all know, dividing by `0` is not allowed in mathematics, and hence this cannot be relevant to their work. In fact knowing `real.div` is the same as knowing mathematical division; any theorem about one translates into a theorem about the other, so having `real.div` is equivalent to having mathematical division. -->

確かに Twitter では混乱を招いているようですね．しかし，証明支援系で数学を行うときに混乱することはありません．**数学者は0で割り算をしません**から，`real.div` と数学的割り算（`1/0` は定義されない）の違いに気づくことはないのです．実際，Lean における `1/0` の定義を気にしている数学者がいたとしたら，その理由を尋ねられるでしょう．知っての通り，数学では `0` での割り算は許されていませんから，数学をする上では関係ないはずだからです．実のところ，`real.div` と数学的な割り算は同じと考えてよいものです．すべての `real.div` に関する定理は数学的な割り算に翻訳できますし，逆も然りです．`real.div` を実装することは，数学的な割り算を実装することと等価です．

<!-- ## This convention is stupid though! -->
## こんな慣例ばかげてる！

<!-- It gets worse. There’s a subtraction `nat.sub` defined on the natural numbers $\lbrace 0,1,2,\ldots \rbrace$, with notation `x - y`, and it eats two natural numbers and spits out another natural number. If `x` and `y` are terms of type `ℕ` and `x < y`, then `x - y` will be `0`. There’s a function called `real.sqrt` which takes as input a real number, and outputs a real number. If you give it $2$, it outputs $\sqrt{2}$. I don’t know what happens if you give it the input $-1$, beyond the fact that it is guaranteed to output a real number. Maybe it’s $0$. Maybe it’s $1$. Maybe it’s $37$. I don’t care. I am a mathematician, and if I want to take the square root of a negative real number, I won’t use `real.sqrt` because I don’t want an answer in the reals, and the type of `real.sqrt` is `ℝ → ℝ`. -->

ゼロ除算以外にも例があります．自然数 $\lbrace 0,1,2,\ldots \rbrace$ には引き算 `nat.sub` が定義されていて，`x - y` と書きます．これは2つの自然数を与えられたら1つの自然数を返します．仮に `x < y` だったとしたら，`x - y` は `0` です．`real.sqrt` という関数もあり，これは実数を1つ与えられたら実数を1つ返します．$2$ を入力したら出力は $\sqrt{2}$ です．`-1` を入力したら，何が返されるかはよくわかりませんが実数が返ってくることは保証されています．$0$ かもしれませんし，$1$ かもしれません．$37$ かも? どうだっていいことです．私は数学者であり，負の実数の平方根を取りたい場合 `real.sqrt` は使いません．なぜなら実数で答えを出したくないからです．一方で `real.sqrt` の型は `ℝ → ℝ` です．

<!-- ## Why can’t you just do it the sensible way like mathematicians do? -->
## 数学者がやるような常識的な方法では何がまずいの？

<!-- Great question! I tried this in 2017! Turns out it’s really inconvenient in a theorem prover! -->

素晴らしい質問ですね．2017 年に私は試してみました．証明支援系ではとても不便な方法だということがわかりました！

<!-- Here’s how I learnt Lean. I came at it as a “normal mathematician”, who was thinking about integrating Lean into their undergraduate introduction to proof course. I had no prior experience with theorem provers, and no formal background in programming. As a feasibility study, I tried to use Lean to do all the problem sheets which I was planning on giving the undergraduates. This was back in 2017 when Lean’s maths library was much smaller, and `real.sqrt` did not yet exist. However the basic theory of sups and infs had been formalised, so I defined `real.sqrt x`, for `x` non-negative, to be $Sup\lbrace y\in\mathbb{R} ∣ y^2\leq x\rbrace$, and proved the basic theorems that one would want in an interface for a square root function, such as $\sqrt{ab}=\sqrt{a}\sqrt{b}$ and $\sqrt{a^2}=a$ and $\sqrt{a^2b}=a\sqrt{b}$ and so on (here $a,b$ are non-negative reals, the only reals which my function would accept). -->

私が Lean を学んでいたときのことです．私は「普通の数学者」として，学部の証明入門コースに Lean を取り入れようと考えていました．私は当時定理証明の経験がなく, プログラミングの正式な素養もありませんでした．Lean での授業が実現可能か調査するために，学部生に配る予定だった問題集をすべて Lean でやってみました．これは Lean の数学ライブラリがもっと小さくて，`real.sqrt` がまだ存在していなかった 2017 年当時の話です．しかし sup と inf の基本理論は形式化されていたので，私は 0 以上の `x` に対して `real.sqrt x` を $\mathrm{Sup}\lbrace y\in\mathbb{R} ∣ y^2\leq x\rbrace$ として定義しました．そして，平方根関数を扱うのに必要な $\sqrt{ab}=\sqrt{a}\sqrt{b}$ や $\sqrt{a^2}=a$ や $\sqrt{a^2b}=a\sqrt{b}$ などの基本的な定理を証明しました．(ここで $a, b$ は非負実数です．私の定義した平方根関数は非負実数しか受け付けません．)

<!-- I then set out to prove $\sqrt{2}+\sqrt{3}<\sqrt{10}$, a question on a problem sheet from my course. The students are told not to use a calculator, and asked to find a proof which only uses algebraic manipulations, i.e. the interface for `real.sqrt`. Of course, the way I had set things up, **every time** I used the $\sqrt{\phantom{2}}$ symbol I had to supply a proof that what I was taking the square root of was non-negative. Every time the symbol occurred in my proof. Even if I had proved `2 > 0` on the previous line, I had to prove it again on this line, because this line also had a $\sqrt{2}$ in. Of course the proof is just by `norm_num`, but that was 10 characters which I soon got sick of typing. -->

そして私の授業の問題集にあった $\sqrt{2}+\sqrt{3}<\sqrt{10}$ に取り掛かりました．電卓を使わずに，代数的な操作だけを使って証明せよという問題です．つまり，`real.sqrt` を使う問題です．言うまでもなく，私が使った定義では，$\sqrt{\phantom{2}}$ を使うたびに**毎回**平方根の中が非負であることを証明する必要があります．毎度毎度平方根が現れるたびにです．たとえ前の行で `2 > 0` を証明していても，次の行で $\sqrt{2}$ があればまた示す必要があるのです．もちろん証明は `norm_num` で済むのですが，私はすぐにこれをタイプするのが嫌になりました．

<!-- I then moaned about this on the Lean chat, was mocked for my silly mathematician conventions, and shown the idiomatic Lean way to do it. The idiomatic way to do it is to allow garbage inputs like negative numbers into your square root function, and return garbage outputs. It is in the **theorems** where one puts the non-negativity hypotheses. For example, the statement of the theorem that $\sqrt{ab}=\sqrt{a}\sqrt{b}$ has the hypotheses that $a,b\geq 0$. Note that it does not also have the hypothesis that $ab\geq 0$, as one can deduce this within the proof and not bother the user with it. This is in contrast to the mathematicians’ approach, where the proof that $ab\geq 0$ would also need to be supplied because it is in some sense part of the $\sqrt{\phantom{2}}$ notation. -->

Lean チャットでこのことを愚痴ったところ，数学者の慣習の愚かさを指摘され，Lean 流の慣用的なやり方を教えられました．それは，負の数のようなゴミ入力を平方根関数に許可し，ゴミ出力を返すことです．非負の仮定は**定理**の中に置きます．例えば，$\sqrt{ab}=\sqrt{a}\sqrt{b}$ という定理には, $a,b\geq 0$ であるという仮定を持たせます．$ab\geq 0$ という仮定は持たせないことに注意してください．というのも，証明の中で導くことができるので，この定理のユーザにそれを示させる必要がないからです．これは関数に仮定を持たせる数学者流のアプローチとは対照的です．数学者流では，$\sqrt{\phantom{2}}$ という表記自体が非負性を要求するので，$ab\geq 0$ も示す必要がありました．

<!-- ## So you’re saying this crazy way is actually better? -->
## じゃあ, このクレイジーなやり方の方が本当はいいってこと？

<!-- No, not really. I’m saying that it is (a) mathematically equivalent to what we mathematicians currently do and (b) simply more convenient when formalising mathematics in dependent type theory. -->

いや, そこまで言っていません．私が言っているのは，(a) 私たち数学者が現在行っていることと数学的に同等であり，(b) 依存型理論で数学を形式化する際に，単純により便利であるということです．

<!-- What actually is a field anyway? For a mathematician, a field is a set $F$ equipped with $0,1,a+b,-a,a\times b,a^{-1}$ where the inversion function $a^{-1}$ is only defined for non-zero $a$. The non-zero elements of a field form a group, so we have axioms such as $x\times x^{-1}=1$ for $x\not=0$ (and this doesn’t even make sense for $x=0$). Let’s say we encountered an alien species, who had also discovered fields, but their set-up involved a function $\iota :F\to F$ instead of our $x^{-1}$. Their $\iota$ was defined, using our notation, by $\iota(x)=x^{-1}$ for $x\not=0$, and $\iota(0)=0$. Their axioms are of course just the same as ours, for example they have $x\times \iota(x)=1$ for $x\not=0$. They have an extra axiom $\iota(0)=0$, but this is no big deal. It’s swings and roundabouts — they define $a/b:=a\times\iota(b)$ and their theorem $(a+b)/c=a/c+b/c$ doesn’t require $c\not=0$, whereas ours does. They are simply using slightly different notation to express the same idea. Their $\iota$ is discontinuous. Ours is not defined everywhere. But there is a canonical isomorphism of categories between our category of fields and theirs. There is no difference mathematically between the two set-ups. -->

体とは何かを考えてみましょう．数学では，体とは $0,1,a+b,-a,a\times b,a^{-1}$ を持つ集合 $F$ のことです．ただし逆元を取る操作 $a^{-1}$ はゼロでない $a$ に対してのみ定義されます．体のゼロでない要素は群を形成し，$x\not=0$ に対して $x\times x^{-1}=1$ という公理を満たします．($x = 0$ のときこれは意味をなしません)ここで我々が異星人と遭遇し，その異星人も体を発見していたとしましょう．しかし異星人の定義では，$x^{-1}$ ではなく関数 $\iota :F\to F$ を使用していたとします．その $\iota$ は，我々の表記法を用いると $x\not=0$ のとき $\iota(x)=x^{-1}$ で，$\iota(0)=0$ を満たすとします．もちろん異星人の公理は我々のものと同じで，たとえば $x\not=0$ に対して $x\times \iota(x)=1$ が成り立っています．異星人の体は追加の公理 $\iota(0)=0$ を持っていますが，これは大きな問題にはなりません．一長一短です． ーー 異星人流には $a/b:=a\times\iota(b)$ と定義され，彼らの定理 $(a+b)/c=a/c+b/c$ には我々が必要とするような $c\not=0$ という仮定が必要ありません．同じアイデアを表現するために，少し違った表記を使っているだけなのです．異星人の $\iota$ は不連続です．我々のは体全体で定義されていません．しかし彼らの体の圏と我々の体の圏の間には，正準な同型があります．2つの定義の間に数学的な違いはありません．

<!-- Lean uses the alien species convention. The aliens’ `\iota` is Lean’s `field.inv` , and Lean’s `field.div x y` is defined to be `field.mul (x, field.inv y)`. -->

Lean は今の話でいう異星人流の慣例を使っています．異星人の $ι$ は Lean の `field.inv` に相当します．そして体での割り算は，Lean では `field.div x y` であり，これは `field.mul (x, field.inv y)` として定義されています．

<!-- ## OK so I can see that it can be made to work. Why do I still feel a bit uncomfortable about all this? -->
## オーケー，それで上手くいくことはわかった. でも何故まだ違和感を感じるんだろう？

<!-- It’s probably for the following reason. You are imagining that a computer proof checker will be checking your work, and in particular checking to see if you ever divided by zero, and if you did then you expect it to throw an error saying that your proof is invalid. What you need to internalise is that Lean is just using that function $f$ above, defined by $f(x,y)=x/y$ for $y\not=0$ and $f(x,0)=0$. In particular you cannot prove false things by applying $f$ to an input of the form $(x,0)$, because the way to get a contradiction by dividing by zero and then continuing will involve invoking theorems which are true for mathematical division but which are not true for $f$. For example perhaps a mathematician would say $a/a=1$ is true for all $a$, with the implicit assumption that $a\not=0$ and that this can be inferred from the notation. Lean’s theorem that `real.div a a = 1` is only proved under the assumption that $a\not=0$, so the theorem cannot be invoked if $a=0$. In other words, the problem simply shows up at a different point in the argument. Lean won’t accept your proof of $1=2$ which sneakily divides by $0$ on line 8, but the failure will occur at a different point in the argument. The failure will still however be the assertion that you have a denominator which you have not proved is nonzero. It will simply not occur at the point when you do the division, it will occur at the point where you invoke the theorem which is not true for `real.div`. -->

それはおそらく次のような理由からでしょう．コンピュータの証明チェッカーがあなたのコードをチェックし, 特にゼロで割ったことがあるかどうかをチェックし，もし割ったことがあれば，証明が無効であるというエラーを投げるだろうと期待していませんか．Lean は上記の $y\not=0$ に対しては $f(x,y)=x/y$ であり，$y=0$ のとき $f(x,0)=0$ と定義された関数 $f$ を使っているだけであることを思い出す必要があります．特に, $(x,0)$ の形の入力に $f$ を適用することで誤ったことを証明することはできません．数学の割り算ではゼロで割ってから続けることで矛盾が得られますが，$f$ では得られません．例えば, 数学者が $a/a=1$ はすべての $a$ に対して真であると言っているとき，$a\not=0$ という暗黙の前提があり，これは表記から推測できます．`real.div a a = 1` という Lean の定理は, $a\not=0$という仮定の下でのみ証明されるので, $a=0$ の場合は定理を使えません．言い換えれば，ゼロ除算の問題が現れる場所が変わるだけなのです．Lean は $0$ でこっそり割ることで $1=2$ を示そうとする証明を受け入れませんが，エラーはゼロで割るときではなく別のところで起きるでしょう．ゼロでないことを証明していない分母があるということが問題になるのは変わりません．問題は単に割り算をした時点で起こるのではなく，`real.div` に関して正しくない定理を呼び出した時点で起こるのです．

<!-- Thanks to Jim Propp and Alex Kontorovich for bringing this up on Twitter. I hope that this clarifies things. -->
ツイッターでこの件を取り上げてくれた Jim Propp と Alex Kontorovich に感謝します．これで物事が明確になることを願っています．

---

訳者: [@Seasawher](https://github.com/Seasawher)