# ToyC 编译器实验报告

## 1. 实验目的

本实验的目标是独立实现一个 ToyC 到 `RISC-V32` 汇编的编译器，并在此基础上逐步加入优化能力，使生成代码在正确性的前提下尽量接近工业编译器 `-O2` 的效果。具体目标包括：

- 完成词法分析、语法分析、语义分析、代码生成等完整编译流程。
- 保证编译器从标准输入读取 ToyC 程序、向标准输出输出汇编程序。
- 在不依赖 Clang、LLVM 等现成编译框架的前提下，自主实现中间表示、控制流图和优化流水线。
- 通过自动化脚本回归公开样例、隐藏风格样例和非法语义样例。
- 逐步建立从“功能正确”到“中端优化”再到“后端性能收尾”的完整工程意识。

## 2. 项目概况

ToyC 相比完整 C 语言省去了数组、指针、I/O、多文件编译等特性，因此本项目的难点并不在于复杂内存模型，而主要集中在以下几个方面：

- 结构化语法到显式控制流的 lowering。
- `const`、作用域、函数签名、返回路径等语义约束检查。
- 短路逻辑、循环控制和函数调用的正确翻译。
- 在 CFG 上做 copy/GVN/DCE/loop 等优化。
- 在最终 `RISC-V32` 汇编层面减少无效 move、spill/reload 和冗余分支。

当前项目已经形成如下主流水线：

```text
ToyC source
  -> Lexer / Parser
  -> AST
  -> Semantic Analysis
  -> TCG lowering
  -> CFG construction
  -> optimize_cfg (-opt)
  -> RISC-V32 code generation
  -> asm peephole cleanup
```

## 3. 小组分工

以下分工可按最终组员实际情况替换姓名：

- 组员 A：词法分析、语法分析、错误定位。
- 组员 B：语义分析、符号表、`const` 检查、返回路径检查。
- 组员 C：中间表示、TCG lowering、CFG 构建。
- 组员 D：后端代码生成、优化实验、测试脚本与实验报告整理。

在实际开发中，优化阶段的工作具有很强的交叉性，因此中后期大量工作采用了共同调试、共同回归的方式推进。

## 4. 系统结构与实现思路

### 4.1 前端总体设计

前端目标是把源程序稳定地转成结构统一的 AST，并尽可能早地发现语法错误与明显语义错误。为此项目采用分层结构：

- `lib/lexer_impl.mll` / `lib/lexer.ml`
  - 基于 `ocamllex` 的词法分析器。
- `lib/grammar.mly` / `lib/parser.ml`
  - 基于 `ocamlyacc` 的语法分析器。
- `lib/ast.ml`
  - 抽象语法树定义。
- `lib/semant.ml`
  - 语义分析与全局/局部环境维护。

这种分层的价值在于：后端和优化阶段不需要重新理解源代码结构，所有结构性信息都已经在 AST 和语义分析阶段被规整过。

### 4.2 词法与语法分析

词法分析器负责识别：

- 标识符、整数常量、关键字。
- 运算符和分隔符。
- 单行/多行注释。
- 空白与换行。

语法分析器负责建立如下核心结构：

- 全局变量/常量定义。
- 函数定义。
- `if/else`、`while`、`break`、`continue`、`return`。
- 赋值语句与表达式语句。
- 算术、关系、逻辑表达式。

项目通过优先级声明和 `%prec` 规则解决了表达式结合性和 dangling else 问题，使 AST 层的结构足够稳定。

### 4.3 AST 设计

AST 并不追求完全贴近源代码书写形式，而是追求后续处理的统一性。典型定义如下：

```ocaml
type expr =
  | Int of int64
  | Var of string
  | Call of string * expr list
  | Unary of unop * expr
  | Binary of binop * expr * expr

type stmt =
  | Block of stmt list
  | Empty
  | Expr of expr
  | Assign of string * expr
  | Decl of decl
  | If of expr * stmt * stmt option
  | While of expr * stmt
  | Break
  | Continue
  | Return of expr option
```

这样的结构为后续语义检查、常量传播和 lowering 提供了稳定基础。

### 4.4 语义分析

语义分析层负责检查课程语言规范，包括：

- `main` 必须为 `int main()`。
- 函数调用只能调用已定义函数，且参数个数匹配。
- 变量必须先声明后使用。
- `const` 不能被重新赋值。
- `break` / `continue` 只能用于循环内部。
- `int` 函数必须保证所有路径都有返回值。
- `void` 值不能作为表达式值继续参与运算。
- 全局初始化和 `const` 初始化必须可在编译期求值。

这里最重要的一个工程选择是：把所有“语言规则”尽量收敛在 `semant.ml` 内部，而不是等到 codegen 阶段再兜底。这样做显著降低了后端复杂度。

### 4.5 中间表示与 CFG

项目没有直接从 AST 生成汇编，而是显式引入了中间表示：

- `lib/tcg.ml`
  - 把 AST lowering 成接近三地址形式的低层指令。
- `lib/cfg.ml`
  - 按 terminator 划分基本块并重建控制流图。

核心思想是把结构化语法翻译成显式的：

- 取值。
- 算术/逻辑运算。
- Load / Store。
- Call。
- 条件跳转 / 无条件跳转。

这样后续优化就不需要在 AST 层“猜语义”，而可以直接在 CFG 上做数据流和循环分析。

### 4.6 短路逻辑 lowering

`&&` 和 `||` 没有被当成普通二元运算，而是被 lowering 成控制流。典型逻辑类似：

```ocaml
| Binary (LAnd, a, b) ->
    let mid_l = fresh_label builder "and_rhs" in
    lower_cond env builder a mid_l false_l;
    emit builder (Label mid_l);
    lower_cond env builder b true_l false_l
| Binary (LOr, a, b) ->
    let mid_l = fresh_label builder "or_rhs" in
    lower_cond env builder a true_l mid_l;
    emit builder (Label mid_l);
    lower_cond env builder b true_l false_l
```

这保证了短路语义真正成立，而不是依赖“先都算完再模拟布尔值”。

### 4.7 后端代码生成

`lib/codegen.ml` 负责：

- 栈帧布局。
- 局部变量与临时值的 home 分配。
- 参数传递与返回值。
- 全局变量地址访问。
- CFG 到 `RISC-V32` 汇编的最终翻译。

当前后端已经不再是纯玩具版本，而是具备：

- interval / spill weight 风格的寄存器分配。
- loop-carried 分数与热点值偏向寄存器。
- 局部 copy 清理与部分 compare/branch 融合。

收尾工作由 `lib/asm_opt.ml` 完成，主要负责删掉简单的冗余汇编形式。

## 5. normal 模式的实现重点

在只讨论 normal 模式时，本项目最重要的目标是：

- 语义正确。
- 翻译结构清晰。
- 后续可扩展。

为此 normal 模式下也已经具备以下工程特征：

- 清晰的前中后端边界。
- 显式 CFG 而非直接拼汇编。
- 短路逻辑与函数调用的正确控制流翻译。
- 统一的栈帧与参数布局。
- 自动化 smoke/invalid 测试脚本。

这意味着后续优化并不是在一份“只能勉强跑起来”的代码上硬补，而是在一条结构化主线上逐步扩展。

## 6. 优化设计与演进

这一部分是整个项目最重要的内容。与基础 normal 模式相比，优化阶段的工作量更大、调试更复杂，也更能体现编译原理课程中“中端 + 后端协同”的核心思想。

### 6.1 优化流水线的组织方式

项目的 `-opt` 模式不是只在最后做一个 peephole，而是明确拆成三层：

```ocaml
let parsed = Parser.parse source in
let ast = if has_opt_flag () then Opt.optimize_ast parsed else parsed in
let analysis = Semant.analyze ast in
let tcg = Tcg.of_analysis analysis in
let cfg = Cfg.of_tcg tcg in
let cfg = if has_opt_flag () then Opt.optimize_cfg analysis cfg else cfg in
let asm = Codegen.generate analysis cfg in
print_string (if has_opt_flag () then Asm_opt.peephole asm else asm)
```

这三层分别承担不同职责：

- AST 层：尽早清理明显可规约结构。
- CFG 层：做主要的数据流和循环优化。
- 汇编层：做机器级收尾。

这种组织方式极大降低了调试难度，也避免了所有优化都挤在一个阶段导致的复杂度爆炸。

### 6.2 AST 层优化

AST 层主要完成：

- 常量传播。
- 常量折叠。
- 短路表达式提前化简。
- 死分支删除。
- 不可达尾部语句删除。

这部分虽然看起来“基础”，但对后续影响非常大。因为如果 `if (0)`、`if (1)`、`0 && expr`、`1 || expr` 等结构能在 AST 层直接规整掉，后面的 CFG 规模就会明显变小。

AST 层优化主要支撑以下性能点：

- `p01_const`
- `p11_global_const_prop`
- `p12_const_expr_chain`

其中 `p12_const_expr_chain` 能做到满分，说明常量链路规约已经很强。

### 6.3 mem2reg、promotion 与标量优化

在 CFG 层，最先解决的问题是“值是否能以适合优化的形式流动”。为此项目逐步实现了：

- `mem2reg_func`
- `promote_globals_func`
- copy propagation
- dead code elimination
- copy coalescing

只有当大量 local/global place 被提升成更稳定的 temp 形式，后续 GVN、代数规范化和循环分析才真正有发挥空间。

这部分改进主要改善：

- `p02_dead_code`
- `p03_copy`
- `p04_common_subexpr`
- `p08_basic_combined`

其中一个重要经验是：很多看似“代数问题”或“循环问题”，本质上其实是前面值还没有被规整到适合分析的形式。

### 6.4 GVN / CSE

项目中端较早形成了可用的 GVN / CSE 能力。它的目标是将语义等价但重复出现的表达式尽量统一为同一份结果，减少重复计算。

例如：

```c
u = a + b;
v = a + b;
return u * v;
```

理想上可规约为：

```c
t = a + b;
return t * t;
```

这类优化直接对应 `p04_common_subexpr`，也是很多综合性能点的基础能力。

### 6.5 代数规范化

随着优化深入，我们逐渐发现仅靠局部规则如 `x+0`、`x*1` 已经不够，需要建立更统一的代数 canonical form。为此项目后续加入了：

- `general_linear_canonicalize_func`
- `factor_common_mul_func`

重点处理如下形状：

- `(x + a) - a`
- `(x - a) + a`
- `2*x + 3*x`
- `(x + y) - (y + z)`
- `x*b + x*c`

这部分直接对应 `p05_algebra`。当前该项已有明显提升，但与工业编译器相比仍有差距，主要原因是：

- 当前 canonicalization 仍偏向线性整数表达式。
- 和 GVN、loop summary 的联动还不够完全统一。

### 6.6 尾递归消除

`tailrec_elim_func` 是本项目优化阶段最成功的一项结构性变换之一。它专门处理：

- 尾部直接调用自身。
- 调用结果立即返回。
- 参数更新可安全改写为循环回跳。

这项优化并不是“减少几条指令”，而是把递归整体改写为循环，因此收益非常大。它直接推动：

- `p06_tail_recursion`

达到公开评测满分或接近满分水平。

### 6.7 循环优化

循环优化是本项目投入最多、收益也最大的部分之一。当前已经逐步形成了如下能力：

- loop canonicalization
- counted-loop 识别
- runtime symbolic affine summary
- piecewise / threshold 风格循环分段
- 部分 nested loop summary
- 部分 strength reduction

其中最关键的认识是：循环优化不是只靠“再补一个 pattern”就能解决，而需要同时处理：

- CFG 形状是否规整。
- 归纳变量是否识别成功。
- live-out 值是否能 summary。
- 后端是否会把优化收益重新 spill 掉。

#### 当前循环优化的实际效果

这部分直接影响：

- `p07_loop`
- `p08_basic_combined`
- `p09_advanced_graph`
- `p10_advanced_matrix`

目前 `p07` 与 `p08` 已取得较大提升，说明对规则标量循环和综合型中等复杂度循环已经比较有效；但 `p10_advanced_matrix` 仍明显偏低，说明复杂嵌套循环和后端寄存器压力仍然是短板。

### 6.8 后端与机器级优化

这是整个优化阶段后期最重要的一条经验总结：我们一开始长期过度纠结于中间阶段，忽视了后端，因此很多性能损失一直解释不通。

后来通过汇编对比、动态步数统计、copy/move/spill 诊断才确认：

- 很多性能损失并不只是“中端不会化简”。
- 而是中端省下来的收益在后端又被 `move`、`spill/reload`、保守跳转形式吃掉了。

因此后续我们开始更重视：

- 寄存器分配权重。
- hot local 的寄存器常驻倾向。
- copy coalescing 的后端价值。
- compare/branch 融合。
- 汇编级 peephole 收尾。

这一阶段虽然不如尾递归消除那样“单点暴涨”，但它让很多中端优化第一次真正落到了最终汇编性能上。

## 7. 当前性能结果

以下是一轮代表性的公开性能测试结果：

| 测试点 | 结果 | 运行时间 | 性能 | 得分 |
|---|---|---:|---:|---:|
| p01_const | 通过 | 720ms | 43% | 3.58 |
| p02_dead_code | 通过 | 720ms | 41% | 3.46 |
| p03_copy | 通过 | 754ms | 40% | 3.34 |
| p04_common_subexpr | 通过 | 717ms | 48% | 4.01 |
| p05_algebra | 通过 | 667ms | 54% | 4.55 |
| p06_tail_recursion | 通过 | 560ms | 100% | 8.33 |
| p07_loop | 通过 | 615ms | 85% | 7.15 |
| p08_basic_combined | 通过 | 801ms | 64% | 5.34 |
| p09_advanced_graph | 通过 | 1350ms | 67% | 5.65 |
| p10_advanced_matrix | 通过 | 2120ms | 27% | 2.27 |
| p11_global_const_prop | 通过 | 915ms | 65% | 5.45 |
| p12_const_expr_chain | 通过 | 44ms | 100% | 8.33 |

从这些结果可以总结出：

- 常量链、尾递归和规则循环类优化已经形成明显优势。
- 综合类测试 `p08`、图类测试 `p09` 也已经有较强收益。
- 当前最明显的剩余短板是 `p10_advanced_matrix`，也就是更复杂的嵌套循环和更强后端压力场景。

## 8. 优化过程中遇到的主要困难

### 8.1 过分纠结中间阶段，忽视后端

这是本项目最重要的一条反思。早期我们长期把主要精力放在：

- loop 识别。
- affine summary。
- algebra pattern。
- GVN / DCE 联动。

这些工作本身当然是必要的，但如果后端仍然频繁产生：

- 无效 `move`
- 过多 spill / reload
- 栈味很重的热点循环

那么很多中端收益最终会被吞掉。也就是说，性能问题不能只从 `opt.ml` 理解，必须把 `codegen.ml` 和 `asm_opt.ml` 一起纳入诊断。

### 8.2 优化命中率与正确性的矛盾

循环优化尤其如此。很多模式只要再放宽一点，就可能 wrong-code；但如果过度保守，又会导致大量实际样例 miss。

因此整个优化过程都在平衡两件事：

- 如何提升命中率。
- 如何不破坏语义正确性。

### 8.3 优化是联动问题，不是单点问题

例如：

- copy propagation 前需要 canonical form。
- loop summary 前需要 loop canonicalization。
- GVN 后往往还要 DCE。
- 中端优化如果没有后端承接，收益会大量流失。

这意味着优化 pass 的顺序、重跑策略和边界设计本身就是实现难点。

## 9. 当前实现水平评估

就课程项目而言，本仓库当前已经具备比较明显的“完整优化编译器”特征：

- 不是只做词法/语法/语义和简单代码生成。
- 不是只在 AST 层做少量常量折叠。
- 已经形成较完整的 CFG 优化和循环优化框架。
- 已经开始把中端和后端一起当作性能系统来理解。

与 LLVM/Clang `-O2` 相比，当前差距主要体现在：

- 更统一的 SCEV-lite / 标量递推表达层还不够成熟。
- 复杂 nested loop / piecewise recurrence 覆盖还不够广。
- symbolic bound / runtime proof 体系仍偏离散。
- 寄存器分配和机器级 cleanup 仍不够工业化。

但从课程项目的完成度来看，已经明显超出“基础正确”层面，进入了“有体系地追求性能”的阶段。

## 10. 后续可继续改进的方向

如果继续向工业编译器靠拢，最值得投入的方向包括：

- 把循环分析升级为统一的递推表达层，而不是多个 pattern matcher 叠加。
- 做更稳定的 loop simplify / canonicalization / LCSSA-lite。
- 让 symbolic bound 与 runtime proof 体系化。
- 强化 nested loop 和 piecewise summary 的连接能力。
- 继续推进后端寄存器分配、copy cleanup 和 machine-level peephole。

## 11. 总结

本项目完成了一个从 ToyC 到 `RISC-V32` 的完整编译器，并在此基础上实现了较系统的优化框架。实验过程中，我们逐步认识到：

- 正确性是优化的前提。
- 中端优化必须建立在稳定的 IR / CFG 之上。
- 真正拉开差距的不只是“会不会做某个优化”，而是“能否让多层优化协同工作，并最终落到机器代码上”。

从最终结果看，本项目已经在多个性能点上取得显著提升，也为进一步逼近工业级 `-O2` 打下了比较扎实的基础。
