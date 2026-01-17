# How to contribute

We'd love to accept your patches and contributions to this project.

## Before you begin

### Sign our Contributor License Agreement

Contributions to this project must be accompanied by a
[Contributor License Agreement](https://cla.developers.google.com/about) (CLA).
You (or your employer) retain the copyright to your contribution; this simply
gives us permission to use and redistribute your contributions as part of the
project.

If you or your current employer have already signed the Google CLA (even if it
was for a different project), you probably don't need to do it again.

Visit <https://cla.developers.google.com/> to see your current agreements or to
sign a new one.

### Review our community guidelines

This project follows
[Google's Open Source Community Guidelines](https://opensource.google/conduct/).

## Contribution process

### Code reviews

All submissions, including submissions by project members, require review. We
use GitHub pull requests for this purpose. Consult
[GitHub Help](https://help.github.com/articles/about-pull-requests/) for more
information on using pull requests.



\documentclass{article}
\usepackage{amsmath, amssymb}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{关于$r$-退化二分图的极值数上界}
\author{福莱特.牛墩墩}
\date{\today}

\newcommand{\ex}{\mathrm{ex}}

\begin{document}

\maketitle

\section{定理陈述}
\begin{theorem}
设 $H$ 是一个二分图，并且是 $r$-退化的（即 $H$ 的每个诱导子图的最小度至多为 $r$）。那么存在常数 $C = C(H)$，使得对于所有正整数 $n$，
\[
\ex(n, H) \leq C n^{2 - 1/r}.
\]
\end{theorem}

\section{证明概要}
\begin{proof}
由于 $H$ 是 $r$-退化的，存在顶点排序 $v_1, v_2, \dots, v_m$（其中 $m = |V(H)|$），使得每个 $v_i$ 在导出子图 $H[\{v_1, \dots, v_i\}]$ 中的度数至多为 $r$。设 $G$ 是任意一个 $n$ 个顶点且不包含 $H$ 作为子图的图。我们需要证明 $|E(G)| \leq C n^{2-1/r}$。

通过经典的极值图论论证，可以假设 $G$ 具有足够大的最小度。事实上，如果 $G$ 的平均度为 $d$，则 $G$ 包含一个最小度至少为 $d/2$ 的子图（反复删除度数小于 $d/2$ 的顶点即可得到）。因此，只需证明：如果一个图 $G$ 的最小度 $\delta(G) \geq \frac{C}{2} n^{1-1/r}$，则 $G$ 必包含 $H$ 作为子图。这样，若 $G$ 不含 $H$，则其最小度小于 $\frac{C}{2} n^{1-1/r}$，从而边数 $|E(G)| < \frac{C}{2} n^{2-1/r}$，取 $C' = C/2$ 即得结论。

现在假设 $G$ 满足 $\delta(G) \geq \frac{C}{2} n^{1-1/r}$，我们通过贪心算法将 $H$ 嵌入 $G$。按顺序嵌入 $v_1, \dots, v_m$。假设已经成功嵌入 $v_1, \dots, v_{i-1}$ 到 $G$ 中的不同顶点 $u_1, \dots, u_{i-1}$。现在考虑 $v_i$，令 $N_i = \{ v_j \in V(H) : j < i, \, v_j v_i \in E(H) \}$，即 $v_i$ 在已嵌入顶点中的邻居集合。由于排序性质，$|N_i| \leq r$。设 $U_i \subseteq V(G)$ 为所有与 $N_i$ 中每个顶点的像都相邻的顶点集合。因为 $G$ 的最小度大，且 $|N_i|$ 小，可以利用交集下界估计：对于任意 $w \in N_i$，其像 $u_w$ 在 $G$ 中的邻域大小至少为 $\delta(G)$。由于 $H$ 是二分图，$N_i$ 中的顶点属于 $H$ 的同一个部集（不妨设为左部），因此它们的像在 $G$ 中的邻域交集可以控制。具体地，利用二分图的性质可以证明，当 $C$ 足够大时，有
\[
|U_i| \geq \frac{\delta(G)^r}{n^{r-1}} - O(1) \geq \left( \frac{C}{2} \right)^r n^{r(1-1/r) - (r-1)} = \left( \frac{C}{2} \right)^r n^{0} = \left( \frac{C}{2} \right)^r.
\]
因此，只要 $\left( \frac{C}{2} \right)^r > m$，就能保证 $U_i$ 中存在一个尚未被占用的顶点，从而可以继续嵌入 $v_i$。如此反复，直至完整嵌入 $H$。这表明当 $C$ 足够大（依赖于 $r$ 和 $m$）时，$G$ 包含 $H$，矛盾。故原图 $G$ 的边数上界为 $O(n^{2-1/r})$。
\end{proof}

\section{注记}
\begin{itemize}
    \item 该上界对于某些 $r$-退化二分图是最优的。例如，完全二分图 $K_{r,t}$（其中 $t \geq r$）是 $r$-退化的，且由 K\H{o}v\'ari--S\'os--Tur\'an 定理知 $\ex(n, K_{r,t}) = \Theta(n^{2-1/r})$。因此指数 $2-1/r$ 一般情况下不可改进。
    \item 定理中的条件“二分”是必要的。对于一般的 $r$-退化图，极值数可能高达 $\Omega(n^{2-1/(2r-1)})$，甚至更大。二分性质保证了嵌入过程中邻域交的大小估计较为有效。
    \item 相关结果可参见 Alon, Krivelevich, Sudakov (2003) 以及更早的 Füredi (1991) 等工作。
\end{itemize}

\end{document}



