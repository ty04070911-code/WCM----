# WCM Analyzer Pro Ver.22.1

## 安定方式
Safariから公式サイトへ直接アクセスせず、GitHub Actionsが公式CSVを取得します。

```text
公式サイト
  ↓ GitHub Actions
data/wcm_distribution.csv
data/wcm_growth.csv
  ↓ 同一ドメイン
WCM Analyzer Pro
```

## 正しい配置

```text
WCM----
├── index.html
├── style.css
├── app.js
├── manifest.json
├── sw.js
├── data
│   ├── .gitkeep
│   └── update-info.json
├── scripts
│   └── update_wcm_data.py
└── .github
    └── workflows
        └── update-wcm-data.yml
```

## 初回設定

1. ZIPを展開
2. 中身をフォルダ構成ごとGitHubへアップロード
3. Actionsを開く
4. Update WCM CSVを選ぶ
5. Run workflowを押す
6. 緑のチェックになったらdataフォルダを確認

作成されるファイル：

```text
data/wcm_distribution.csv
data/wcm_growth.csv
```

## 権限エラー時

Settings → Actions → General → Workflow permissions  
Read and write permissions を選択して保存します。
