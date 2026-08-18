# ToyC Compiler in OCaml

本项目实现了一个将 ToyC 源程序编译为 `RISC-V32` 汇编代码的编译器。编译器从标准输入读取 ToyC 程序，从标准输出输出汇编结果，使用 `OCaml + Dune + ocamllex + ocamlyacc` 完成前端、语义分析、中端优化和后端代码生成。

当前仓库已经不再是“只做词法/语法/语义”的基础版，而是形成了比较完整的编译流水线：

```text
ToyC source
  -> Lexer / Parser
  -> AST
  -> Semantic Analysis
  -> TCG lowering
  -> CFG construction
  -> Mid-end / Loop / CFG optimization (-opt)
  -> RISC-V32 code generation
  -> Assembly peephole cleanup
```

## 1. 项目特点

- 完整支持 ToyC 的函数、局部/全局变量、`const`、`if/else`、`while`、`break`、`continue`、`return`、短路逻辑等语言结构。
- 具有显式的中间表示边界：`AST -> TCG -> CFG -> ASM`，而不是直接从 AST 拼接汇编字符串。
- `-opt` 模式下已经实现较完整的优化流水线，包括：
  - AST 层常量传播、常量折叠、死分支消除。
  - CFG 层 mem2reg / promotion、copy propagation、DCE、GVN/CSE、代数规范化、尾递归消除。
  - 循环层 canonicalization、counted-loop 识别、symbolic affine summary、部分 nested/piecewise loop 优化。
  - 后端层寄存器分配、局部 coalescing、机器级 peephole 清理。
- 内置 Python 版 `RISC-V32` 子集解释器，可直接对生成汇编做正确性和步数回归。

## 2. 构建

在仓库根目录执行：

```sh
dune build
```

如果本地通过 `opam` 管理 OCaml 环境，可使用：

```sh
opam exec -- dune build
```

## 3. 运行

普通模式：

```sh
dune exec compiler -- < input.tc > output.s
```

优化模式：

```sh
dune exec compiler -- -opt < input.tc > output.s
```

Windows + WSL 环境下常用形式：

```sh
opam exec -- dune exec compiler -- -opt < test/basic.tc > /tmp/basic.s
```

## 4. 仓库结构

核心源码主要位于以下位置：

- `lib/ast.ml`
  - ToyC 抽象语法树定义。
- `lib/lexer_impl.mll`、`lib/lexer.ml`
  - 基于 `ocamllex` 的词法分析器。
- `lib/grammar.mly`、`lib/parser.ml`
  - 基于 `ocamlyacc` 的语法分析器。
- `lib/semant.ml`
  - 语义分析、符号表、`const` 求值、函数签名检查、返回路径检查。
- `lib/tcg.ml`
  - 将结构化语法树 lowering 成显式中间表示。
- `lib/cfg.ml`
  - 构建基本块和控制流图。
- `lib/opt.ml`
  - 中端优化主文件，包含 copy/GVN/DCE/loop/tailrec/symbolic summary 等优化逻辑。
- `lib/codegen.ml`
  - `RISC-V32` 后端代码生成与寄存器/栈槽分配。
- `lib/asm_opt.ml`
  - 汇编层收尾优化。
- `lib/driver.ml`
  - 标准输入输出驱动。
- `bin/compiler.ml`
  - 编译器可执行入口。

## 5. 测试

### 5.1 一键 smoke 测试

```sh
python3 -u tools/run_smoke_tests.py
```

该脚本会：

- 自动构建项目。
- 对 `test/expected.txt` 中列出的样例分别跑 normal / `-opt`。
- 用内置 `RISC-V32` 解释器执行生成汇编。
- 比较 `main` 返回值是否正确。
- 检查 `test/invalid/` 下非法样例是否被拒绝。

### 5.2 测试目录组织

当前 `test/` 不只包含基础公开样例，也包含很多为了定位性能和正确性问题而构造的回归集合，例如：

- `test/hidden_dead/`
- `test/hidden_copy/`
- `test/hidden_loop/`
- `test/hidden_dynamic/`
- `test/hidden_nested/`
- `test/hidden_algebra/`
- `test/hidden_all_located/`
- `test/hidden_six_content/`
- `test/hidden_common_loop/`

这些样例主要用于分别压测死代码删除、copy 优化、循环识别、symbolic bound、nested loop summary、代数规范化等能力。

### 5.3 生成单个测试的优化后汇编

```sh
opam exec -- dune exec compiler -- -opt \
< test/hidden_loop/loop_param_step.tc \
> /tmp/loop_param_step.s
```

### 5.4 调试计数循环优化

```sh
TOYC_DEBUG_COUNTED_LOOPS=1 \
python3 -u tools/run_smoke_tests.py
```

仓库中还包含大量专门诊断脚本，例如：

- `tools/run_copy_diagnose.py`
- `tools/run_algebra_diagnose.py`
- `tools/run_matrix_diagnose.py`
- `tools/run_generic_nested_diagnose.py`
- `tools/profile_loop_rejects.py`

## 6. 当前优化能力概览

相较项目早期版本，目前 `-opt` 已经明显超出“只做常量折叠和 peephole”的水平，主要优化能力包括：

- 前端早期优化
  - 常量传播、常量折叠、短路规约、死分支消除、不可达尾部删除。
- 中端标量优化
  - mem2reg、local/global promotion、copy propagation、copy coalescing、dead code elimination、GVN/CSE。
- 代数规范化
  - 线性表达式规约、常量偏移归并、公共乘法因子整理等。
- 函数级优化
  - 尾递归消除、部分 trivial call fold。
- 循环优化
  - loop canonicalization、counted-loop 检测、runtime symbolic affine summary、部分 diamond/piecewise loop 处理、部分 nested summary。
- 后端优化
  - 寄存器分配、热点局部值偏向寄存器、局部 move cleanup、比较/分支融合、汇编级 peephole。

## 7. 当前项目状态

就当前这版实现而言，编译器已经具备以下特征：

- 功能正确性已稳定通过整套 smoke/invalid 回归。
- 性能上，常量、尾递归、规则循环和一部分综合用例已经有明显优化收益。
- 最突出的剩余短板仍然是更复杂的矩阵/嵌套循环类场景，这类场景对统一递推分析、嵌套 loop summary、后端寄存器分配和机器级代码收尾要求更高。

## 8. 报告与文档

- `REPORT.md`
  - 当前 markdown 版实验报告。
- `tools/project_report_docx_source.md`
  - `docx` 报告正文源。
- `tools/generate_project_report_docx.ps1`
  - 从 markdown 源生成课程报告 `docx` 的 PowerShell 脚本。

生成 `docx`：

```powershell
powershell -ExecutionPolicy Bypass -File tools\generate_project_report_docx.ps1
```

## 9. 说明

本项目明确遵守课程要求：

- 使用 OCaml 实现。
- 构建系统为 Dune。
- 不依赖 Clang/LLVM 等现成编译框架。
- 词法/语法工具链仅使用标准 OCaml 生态中的 `ocamllex` / `ocamlyacc`。

如果后续继续冲性能分，最值得投入的方向主要是：

- 更统一的 SCEV-lite / 标量递推表达层。
- 更稳定的 loop simplify / LCSSA-lite / nested summary。
- 更强的 symbolic bound / runtime proof。
- 更成熟的后端寄存器分配与机器级 cleanup。
