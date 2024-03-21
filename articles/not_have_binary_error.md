---
title: "lake update 時に toolchain does not have the binary というエラーが出たときの対処例"
emoji: "🥯"
type: "tech" # tech: 技術記事 / idea: アイデア
topics: ["lean", "lean4", "定理証明支援系"]
published: true
---

## あらまし

既存プロジェクトの Lean のバージョンと mathlib のバージョンを更新しようとして，`lake update` を実行したところ，以下のようなエラーが出ました．

> toolchain 'leanprover/lean4:v4.7.0-rc2' does not have the binary `~\.elan\toolchains\leanprover--lean4---v4.7.0-rc2\bin\lake.exe`

## 解決策の例

:::message
以下は，その時試して上手くいった方法です．
:::

まず，次のコマンドでツールチェインをアンインストールします．これは，既にインストールされているツールチェインに問題があるかもしれないので，それを解消するためです．

```bash
elan toolchain uninstall leanprover/lean4:v4.7.0-rc2
```

次に，以下のコマンドで再インストールします．

```bash
elan toolchain install leanprover/lean4:v4.7.0-rc2
```

終わったら，再度 `lake update` を実行します．以上です．