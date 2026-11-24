# Third-party software

The original project code is released under Apache License 2.0. [Project license](LICENSE)

The Lake lockfile records the revisions of the libraries used to build the project. [NOTICE](NOTICE) identifies the project files with declared Mathlib adaptations and the additional proof passages that cite a corresponding Mathlib argument. It records the upstream authors, copyright notices and pinned sources. The compiler, Lake packages and binary caches are installed separately.

## Build dependencies

| Component | Version or revision | Repository license |
|---|---|---|
| Lean 4 and Lake | `v4.32.0` | [Apache-2.0](https://github.com/leanprover/lean4/blob/v4.32.0/LICENSE) |
| plausible | `e12c1910fe85` | [Apache-2.0](https://github.com/leanprover-community/plausible/blob/e12c1910fe855cbfc38803cd4e55543906d5fa62/LICENSE) |
| LeanSearchClient | `c5d5b8fe6e51` | [Apache-2.0](https://github.com/leanprover-community/LeanSearchClient/blob/c5d5b8fe6e5158def25cd28eb94e4141ad97c843/LICENSE) |
| importGraph | `7e9612bf0b9e` | [Apache-2.0](https://github.com/leanprover-community/import-graph/blob/7e9612bf0b9ee66db3cb5b9988a35afc706f5a12/LICENSE) |
| ProofWidgets4 | `6e311e2a844d` | [Apache-2.0](https://github.com/leanprover-community/ProofWidgets4/blob/6e311e2a844da9b2cc3971187df2fe0066947b93/LICENSE) |
| aesop | `a7dbf0c63b69` | [Apache-2.0](https://github.com/leanprover-community/aesop/blob/a7dbf0c63b694e47f425f3dcddbc0e178bb432d3/LICENSE) |
| Qq | `38d591e778f1` | [Apache-2.0](https://github.com/leanprover-community/quote4/blob/38d591e778f100aec9762bb582f9c7f55f50e9dc/LICENSE) |
| batteries | `023ce7d62a05` | [Apache-2.0](https://github.com/leanprover-community/batteries/blob/023ce7d62a0531e22a5331e20b587817a80d49ff/LICENSE) |
| Cli | `88679d088c97` | [MIT](https://github.com/leanprover/lean4-cli/blob/88679d088c9720c27ebdf2ba4dafe17341747f94/LICENSE) |
| Mathlib | `81a5d257c8e4` | [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/LICENSE) |

The project carries the license texts for the adapted Mathlib source and the pinned build dependencies in [third_party_licenses](third_party_licenses). The importGraph HTML template has a separate MIT notice, and the Lean binary distribution lists additional components in its own notices. [Template license](https://github.com/leanprover-community/import-graph/blob/7e9612bf0b9ee66db3cb5b9988a35afc706f5a12/html-template/LICENSE_source) · [Lean binary notices](https://github.com/leanprover/lean4/blob/v4.32.0/LICENSES)
