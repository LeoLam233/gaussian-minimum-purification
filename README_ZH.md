# 高斯纠缠纯化的模式数界

作者：Dehao Lin，School of Physics, Sun Yat-sen University, Guangzhou, China。

[论文 v0.1（11 页）](paper/manuscript.pdf) · [英文首页](README.md) · [论证导读](docs/PROOF_GUIDE.md) · [复现说明](REPRODUCIBILITY.md)

本稿证明：对文中假设下的有限模玻色和费米高斯态，在所有有限辅助模式数的高斯纯化上取熵的下确界，可以由两侧辅助模分别匹配各自物理模式数的纯化达到。

前人已经提出并宣称这一模式数限制。本稿的贡献是给出对任意更大有限辅助系统的变分归约、压缩等号导致纯因子的机制，以及最优值存在性证明。它不解决非高斯纯化是否能进一步改善最优值的问题。

先用 Python 运行 scripts/verify_repository.py 校验文件，再按照 REPRODUCIBILITY.md 安装依赖和重放。原始六个验证器及独立密度算符检查保留其原始代码；新入口将计算放到 .local/ 下运行，不改写已固定文件。

三份 AI 审计的核验范围、留存代码问题与未复现统计见 [审计状态](audits/STATUS.md)。目前尚无人类专家或期刊同行复核。论文和源码与已冻结的 v0.1 字节一致。

自有代码采用 MIT，论文与文档采用 CC BY 4.0；第三方材料除外。完整原始冻结档保留在本地，仓库中的来源映射说明每份公开代码与其原始文件的关系。
