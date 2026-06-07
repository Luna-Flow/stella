# theory チュートリアル

Use the Typst note as the narrative overview before diving into elaboration details or extending the proof language.

## 推奨フロー

1. まずリポジトリ README と theory の API 文書を読む。
2. `doc/doc_en.typ` にあるコンストラクタまたは入口から始める。
3. 境界挙動へ依存する前に、既存のテストや例で意味論を確認する。

## 実践ガイド

- 内部ヘルパーではなく、文書化された入口を優先する。
- ランタイム・数値・証明状態の前提を下流コードに明示する。
