# Formal Conjectures (形式化数学猜想库)

<p align="center">
  <a href="README.md">English</a> · <b>简体中文</b>
</p>

[![.github/workflows/push_master.yml](https://github.com/google-deepmind/formal-conjectures/actions/workflows/build-and-docs.yml/badge.svg)](https://github.com/google-deepmind/formal-conjectures/actions/workflows/build-and-docs.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2605.13171-b31b1b.svg)](https://arxiv.org/abs/2605.13171)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/google-deepmind/formal-conjectures)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://leanprover.zulipchat.com/#narrow/channel/524981-Formal-conjectures)

本仓库是基于 [mathlib](https://github.com/leanprover-community/mathlib4) 在 [Lean](https://leanprover.github.io/lean4/doc/whatIsLean.html) 交互式定理证明器中形式化数学猜想命题的集合。

浏览文档：[Formal Conjectures 官方文档](https://google-deepmind.github.io/formal-conjectures/)

加入我们在 leanprover Zulip 上的交流频道：[leanprover Zulip 频道](https://leanprover.zulipchat.com/#narrow/channel/524981-Formal-conjectures)

## 目标 (Goals)

尽管包含完整证明的形式化定理语料库正在不断壮大，但目前仍缺乏仅对**猜想命题本身**进行形式化的开放猜想集合。建立此类集合具有多重重要意义：

*   **成为自动化定理证明器与自动化形式化工具的优质基准（Benchmark）。**
*   **通过形式化阐明猜想的精确数学内涵。**
*   **通过明确亟需的数学定义，推动 `mathlib` 社区的进一步扩展。**

我们希望这一倡议能够成为构建更丰富形式化猜想数据集的基石与种子。

### 关于形式化准确性的说明 (Note on Formalisation Accuracy)

在缺乏证明的情况下对数学命题进行形式化具有天然的挑战性。形式化表述中可能会出现细微的不准确之处，未能完全捕捉原始猜想的微妙语义。为缓解此问题，我们将依赖社区贡献者与维护者的严谨人工审查，并计划定期利用 AlphaProof 辅助识别潜在的形式化偏差。

## 贡献指南 (Contributing)

热烈欢迎各种形式的社区贡献——欢迎添加（或仅提交 Issue 描述）您喜爱的数学猜想。详见 [CONTRIBUTING.md](./CONTRIBUTING.md) 获取完整的贡献指南，涵盖贡献方式、分步流程、文件结构规范、属性标注说明及代码风格规范。

## 使用方法、目录结构与特性 (Usage, Structure & Features)

本项目为 Lean 4 项目，使用 `lake` 进行构建管理，依赖 `mathlib`。您需要先[安装 elan、lake、lean 以及可选的 VS Code](https://leanprover-community.github.io/get_started.html)，然后运行：

```bash
lake exe cache get
lake build
```

### 目录结构 (Directory structure)

项目的目录结构按猜想来源的类型进行组织。其中包含两个特殊目录：

-   `FormalConjecturesUtil`：包含各类实用工具，例如 [`category` 属性](./FormalConjecturesUtil/Attributes/Basic.lean)、[`question` 属性](./FormalConjecturesUtil/Attributes/Basic.lean) 以及部分代码检查器（linters）。
-   `FormalConjecturesForMathlib`：包含未来适宜向上游合并至 [mathlib](https://github.com/leanprover-community/mathlib4) 的代码。此处遵循 mathlib 的目录结构。

关于本仓库命题所使用的 `@[category]`、`@[formal_proof]`、`@[AMS]`、`@[question]` 等属性标注的详细用法，请参阅 [CONTRIBUTING.md](./CONTRIBUTING.md)。

## 版本规范 (Versioning)

本仓库跟踪 mathlib 的每月标签发布版（对应 Lean 的版本发布），而非跟踪 mathlib 的 master 主分支。

为了在添加需要尚未并入 mathlib 的定义的问题命题时最大限度减少阻力，此类定义可先添加至 `FormalConjecturesForMathlib` 目录中。这确保了向 formal-conjectures 添加问题不会受限于 mathlib 的发布周期。

当 `main` 分支更新 `lean-toolchain` 时，GitHub Actions 工作流将遵循 mathlib 的标签规范，自动添加形如 `v4.{X}.{Y}` 的 Git 标签。

稳定的基准快照（Benchmark snapshots）采用 `bench-v{N}-lean4.{X}.{Y}` 格式打标，其中：

-   **`v{N}`（基准版本，Benchmark version）：** 标识基准测试中包含的问题集合。每当添加、移除问题或修正形式化错误时，基准版本号递增。
-   **`lean4.{X}.{Y}`（Lean 版本，Lean version）：** 标识该快照所使用的 Lean 4 工具链版本。

标签具有不可变性：对形式化错误的修复绝不会直接打补丁至现有基准版本中，而是并入下一版本 `v{N+1}`。

## 引用 formal-conjectures (Citing formal-conjectures)

如果您的研究工作使用了 formal-conjectures，请考虑通过以下 BibTeX 条目进行引用：

```bibtex
@misc{FormalConjectures,
  author       = {{The Formal Conjectures Authors}},
  title        = {{T}he {F}ormal {C}onjectures {R}epository},
  year         = {2025},
  url          = {https://github.com/google-deepmind/formal-conjectures},
}

@article{FormalConjecturesPaper,
  authors = {Firsching, Moritz and Lezeau, Paul and Mercuri, Salvatore
    and Horv{\'a}th, Mikl{\'o}s Z and Dillies, Ya{\"e}l and S{\"o}nne, Calle and Wieser, Eric and
    Zhang, Fred and Hubert, Thomas and Ag{\"u}era y Arcas, Blaise and Kohli, Pushmeet},
  title = {{F}ormal {C}onjectures: {A}n {O}pen and {E}volving {B}enchmark for {V}erified {D}iscovery in {M}athematics},
  year = {2026},
  url = {https://arxiv.org/abs/2605.13171v1},
}
```

## 许可证 (Licensing)

Copyright 2025 The Formal Conjectures Authors. 所有软件均在 Apache License 2.0 (Apache 2.0) 许可证下开源；除非遵守 Apache 2.0 许可证，否则您不得使用本文件。您可以在以下网址获取 Apache 2.0 许可证的副本：
https://www.apache.org/licenses/LICENSE-2.0

所有其他材料均采用知识共享署名 4.0 国际许可证 (CC-BY) 进行许可。您可以在以下网址获取 CC-BY 许可证的副本：
https://creativecommons.org/licenses/by/4.0/legalcode。

本仓库内容可能基于第三方来源，且在某些情况下可能包含第三方内容。每个猜想的原始来源均在源文件内的 URL 中注明。第三方内容可能受不同的许可要求约束。特别是：

-   来自维基百科（Wikipedia）文章、MathOverflow 和 OEIS 的材料在知识共享署名-相同方式共享 4.0 国际许可证 (CC-BY-SA 4.0) 下发布。
-   来自 bbchallenge.org 的材料在知识共享署名 4.0 国际许可证 (CC-BY 4.0) 下使用。
-   来自 Equational Theories Project 的材料在 Apache-2.0 许可证下使用。
-   来自 arXiv 的材料在源文件内部 URL 所注明的相关论文适用许可证下使用。

除非适用法律要求或书面同意，根据 Apache 2.0 或 CC-BY 许可证分发的所有软件和材料均按“原样（AS IS）”分发，不附带任何明示或暗示的担保或条件。有关权限和限制的具体语言，请参阅相应许可证。

本仓库不是 Google 的官方正式产品（This is not an official Google product）。

---

> **翻译说明（Translation Disclaimer）**
> 本文档由社区志愿者（[@JasonYeYuhe](https://github.com/JasonYeYuhe)）人工翻译并维护，旨在降低中文开发者的阅读门槛。最后同步日期：2026年10月22日。若译文与英文原版存在任何出入或滞后，请以 [英文原版 (README.md)](README.md) 为准。欢迎通过 PR 协助改进译文！
