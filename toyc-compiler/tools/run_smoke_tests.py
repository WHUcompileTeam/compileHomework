from __future__ import annotations

import math
import re
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEST_DIR = ROOT / "test"

REGS_ORDER = [
    "zero",
    "ra",
    "sp",
    "gp",
    "tp",
    "t0",
    "t1",
    "t2",
    "s0",
    "s1",
    "a0",
    "a1",
    "a2",
    "a3",
    "a4",
    "a5",
    "a6",
    "a7",
    "s2",
    "s3",
    "s4",
    "s5",
    "s6",
    "s7",
    "s8",
    "s9",
    "s10",
    "s11",
    "t3",
    "t4",
    "t5",
    "t6",
]

ALIASES = {"x0": "zero", "fp": "s0"}
ALIASES.update({f"x{i}": name for i, name in enumerate(REGS_ORDER)})
ALIASES.update({name: name for name in REGS_ORDER})


def i32(value: int) -> int:
    value &= 0xFFFFFFFF
    return value - 0x100000000 if value & 0x80000000 else value


def u32(value: int) -> int:
    return value & 0xFFFFFFFF


def exit_code(value: int) -> int:
    return value & 0xFF


def regname(reg: str) -> str:
    return ALIASES[reg]


def split_ops(rest: str) -> list[str]:
    return [part.strip() for part in rest.split(",")]


def parse_mem(text: str) -> tuple[int, str]:
    match = re.fullmatch(r"(-?\d+)\(([^)]+)\)", text.strip())
    if not match:
        raise ValueError(f"bad memory operand: {text}")
    return int(match.group(1)), regname(match.group(2))


def compiler_commands() -> list[list[str]]:
    commands: list[list[str]] = []
    for rel in (
        "_build/default/bin/compiler.exe",
        "_build/default/bin/main.exe",
    ):
        candidate = ROOT / rel
        if candidate.exists():
            commands.append([str(candidate)])
    commands.extend(
        [
            ["opam", "exec", "--", "dune", "exec", "compiler", "--"],
            ["opam", "exec", "--", "dune", "exec", "main", "--"],
        ]
    )
    return commands


def compile_source(path: Path, opt: bool) -> str:
    cmd = ["opam", "exec", "--", "dune", "exec", "compiler", "--"]
    if opt:
        cmd.append("-opt")

    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        input=path.read_text(encoding="utf-8"),
        text=True,
        capture_output=True,
    )

    # 显示编译器的调试输出
    if proc.stderr:
        print(proc.stderr, end="")

    if proc.returncode != 0:
        raise RuntimeError(f"{path.name} failed to compile:\n{proc.stderr}")

    return proc.stdout

def compile_expect_failure(path: Path) -> None:
    proc = subprocess.run(
        ["opam", "exec", "--", "dune", "exec", "compiler", "--"],
        cwd=ROOT,
        input=path.read_text(encoding="utf-8"),
        text=True,
        capture_output=True,
    )
    if proc.returncode == 0:
        raise RuntimeError(f"{path.name} unexpectedly compiled successfully")


def compile_source(path: Path, opt: bool) -> str:
    errors: list[str] = []
    for base_cmd in compiler_commands():
        cmd = list(base_cmd)
        if opt:
            cmd.append("-opt")

        try:
            proc = subprocess.run(
                cmd,
                cwd=ROOT,
                input=path.read_text(encoding="utf-8"),
                text=True,
                capture_output=True,
            )
        except FileNotFoundError as ex:
            errors.append(f"{' '.join(cmd)}: {ex}")
            continue

        if proc.stderr:
            print(proc.stderr, end="")

        if proc.returncode == 0:
            return proc.stdout

        errors.append(f"{' '.join(cmd)}:\n{proc.stderr}")

    raise RuntimeError(f"{path.name} failed to compile:\n" + "\n\n".join(errors))


def compile_expect_failure(path: Path) -> None:
    errors: list[str] = []
    for cmd in compiler_commands():
        try:
            proc = subprocess.run(
                cmd,
                cwd=ROOT,
                input=path.read_text(encoding="utf-8"),
                text=True,
                capture_output=True,
            )
        except FileNotFoundError as ex:
            errors.append(f"{' '.join(cmd)}: {ex}")
            continue
        if proc.returncode != 0:
            return
        errors.append(f"{' '.join(cmd)} unexpectedly succeeded")
    raise RuntimeError(f"{path.name} unexpectedly compiled successfully:\n" + "\n".join(errors))


def load_program(asm: str):
    text = []
    labels: dict[str, int] = {}
    data_labels: dict[str, int] = {}
    memory: dict[int, int] = {}
    section = None
    data_addr = 0x200000
    for raw in asm.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith((".option", ".align", ".globl")):
            continue
        if line == ".text":
            section = "text"
            continue
        if line == ".data":
            section = "data"
            continue
        if line.endswith(":"):
            label = line[:-1]
            if section == "data":
                data_labels[label] = data_addr
            else:
                labels[label] = len(text)
            continue
        if section == "data":
            if line.startswith(".word"):
                memory[data_addr] = i32(int(line.split()[1]))
                data_addr += 4
            continue
        if section == "text":
            parts = line.split(None, 1)
            text.append((parts[0], split_ops(parts[1]) if len(parts) > 1 else []))
    return text, labels, data_labels, memory


def run_asm(
    asm: str, limit: int = 50_000_000
) -> tuple[int, int, Counter[str], Counter[str]]:
    text, labels, data_labels, memory = load_program(asm)
    regs = {name: 0 for name in REGS_ORDER}
    regs["sp"] = 0x100000
    regs["ra"] = -1
    pc = labels["main"]
    steps = 0
    dyn_ops: Counter[str] = Counter()
    divrem_consts: Counter[str] = Counter()
    mul_consts: Counter[str] = Counter()
    li_profile: Counter[str] = Counter()
    known_const: dict[str, int] = {}

    def read(reg: str) -> int:
        name = regname(reg)
        return 0 if name == "zero" else regs[name]

    def write(reg: str, value: int) -> None:
        name = regname(reg)
        if name != "zero":
            regs[name] = i32(value)
            known_const.pop(name, None)

    while pc != -1:
        if steps > limit:
            raise RuntimeError("RISC-V subset interpreter step limit exceeded")
        steps += 1
        op, args = text[pc]
        dyn_ops[op] += 1
        next_pc = pc + 1

        if op == "addi":
            write(args[0], read(args[1]) + int(args[2]))
        elif op == "add":
            write(args[0], read(args[1]) + read(args[2]))
        elif op == "sub":
            write(args[0], read(args[1]) - read(args[2]))
        elif op == "mul":
            lhs_name = regname(args[1])
            rhs_name = regname(args[2])
            lhs_const = known_const.get(lhs_name)
            rhs_const = known_const.get(rhs_name)

            if lhs_const is not None and rhs_const is not None:
                mul_consts[f"both:{lhs_const}:{rhs_const}"] += 1
            elif lhs_const is not None:
                mul_consts[f"lhs:{lhs_const}"] += 1
            elif rhs_const is not None:
                mul_consts[f"rhs:{rhs_const}"] += 1
            else:
                mul_consts["variable"] += 1

            write(args[0], read(args[1]) * read(args[2]))
        elif op == "div":
            divisor_name = regname(args[2])
            if divisor_name in known_const:
                c = known_const[divisor_name]
                divrem_consts[f"div:{c}"] += 1
            a, b = read(args[1]), read(args[2])
            write(args[0], math.trunc(a / b))
        elif op == "rem":
            divisor_name = regname(args[2])
            if divisor_name in known_const:
                c = known_const[divisor_name]
                divrem_consts[f"rem:{c}"] += 1
            a, b = read(args[1]), read(args[2])
            q = math.trunc(a / b)
            write(args[0], a - q * b)
        elif op == "slt":
            write(args[0], 1 if read(args[1]) < read(args[2]) else 0)
        elif op == "sltu":
            write(args[0], 1 if u32(read(args[1])) < u32(read(args[2])) else 0)
        elif op == "slti":
            # RV32I signed register-vs-immediate comparison.
            # read() already returns an i32-signed register value.
            write(args[0], 1 if read(args[1]) < int(args[2]) else 0)
        elif op == "sltiu":
            # SLTIU sign-extends its 12-bit immediate first, then performs
            # an unsigned comparison. Converting through u32 also handles
            # negative immediates correctly.
            write(args[0], 1 if u32(read(args[1])) < u32(int(args[2])) else 0)
        elif op == "slli":
            shamt = int(args[2])
            if not 0 <= shamt < 32:
                raise RuntimeError(f"bad RV32 slli shift amount: {shamt}")
            write(args[0], u32(read(args[1])) << shamt)
        elif op == "srli":
            shamt = int(args[2])
            if not 0 <= shamt < 32:
                raise RuntimeError(f"bad RV32 srli shift amount: {shamt}")
            write(args[0], u32(read(args[1])) >> shamt)
        elif op == "srai":
            shamt = int(args[2])
            if not 0 <= shamt < 32:
                raise RuntimeError(f"bad RV32 srai shift amount: {shamt}")
            # read() is already signed i32; Python >> is arithmetic.
            write(args[0], read(args[1]) >> shamt)
        elif op == "andi":
            write(args[0], read(args[1]) & int(args[2]))
        elif op == "xor":
            write(args[0], read(args[1]) ^ read(args[2]))
        elif op == "xori":
            write(args[0], read(args[1]) ^ int(args[2]))
        elif op == "li":
            imm = int(args[1])

            # Profile the immediately following consumer when it directly
            # mentions the LI destination.  This captures the codegen's
            # common rematerialize-then-use pattern without changing
            # execution semantics.
            dst_name = regname(args[0])
            next_kind = "no-direct"
            if pc + 1 < len(text):
                next_op, next_args = text[pc + 1]
                normalized_next_args = []
                for arg in next_args:
                    try:
                        normalized_next_args.append(regname(arg))
                    except KeyError:
                        normalized_next_args.append(arg)
                if dst_name in normalized_next_args:
                    next_kind = next_op

            li_profile[f"{imm}:{next_kind}"] += 1

            write(args[0], imm)
            if dst_name != "zero":
                known_const[dst_name] = i32(imm)
        elif op == "neg":
            write(args[0], -read(args[1]))
        elif op == "la":
            write(args[0], data_labels[args[1]])
        elif op == "lw":
            if len(args) == 2 and args[1] in data_labels:
                # GNU RISC-V pseudo: lw rd, symbol
                write(args[0], memory.get(data_labels[args[1]], 0))
            else:
                off, base = parse_mem(args[1])
                write(args[0], memory.get(read(base) + off, 0))
        elif op == "sw":
            if len(args) == 3 and args[1] in data_labels:
                # GNU RISC-V pseudo: sw rs, symbol, scratch
                # The scratch register is backend-reserved and its exact
                # relocation-intermediate value is semantically unobservable.
                memory[data_labels[args[1]]] = i32(read(args[0]))
            else:
                off, base = parse_mem(args[1])
                memory[read(base) + off] = i32(read(args[0]))
        elif op == "beqz":
            if read(args[0]) == 0:
                next_pc = labels[args[1]]
        elif op == "bnez":
            if read(args[0]) != 0:
                next_pc = labels[args[1]]
        elif op == "beq":
            if read(args[0]) == read(args[1]):
                next_pc = labels[args[2]]
        elif op == "bne":
            if read(args[0]) != read(args[1]):
                next_pc = labels[args[2]]
        elif op == "blt":
            if read(args[0]) < read(args[1]):
                next_pc = labels[args[2]]
        elif op == "bge":
            if read(args[0]) >= read(args[1]):
                next_pc = labels[args[2]]
        elif op == "j":
            next_pc = labels[args[0]]
        elif op == "call":
            write("ra", pc + 1)
            next_pc = labels[args[0]]
        elif op == "ret":
            next_pc = read("ra")
        else:
            raise RuntimeError(f"unsupported emitted instruction: {op}")

        pc = next_pc

    return (
        regs["a0"] & 0xFF,
        steps,
        dyn_ops,
        divrem_consts,
        mul_consts,
        li_profile,
    )


def load_expected() -> dict[str, int]:
    def parse_expected_file(path: Path, expected: dict[str, int]) -> None:
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            name, value = line.split()
            expected[name] = int(value)

    expected: dict[str, int] = {}
    parse_expected_file(TEST_DIR / "expected.txt", expected)

    for fragment in sorted(TEST_DIR.rglob("expected_fragment.txt")):
        parse_expected_file(fragment, expected)

    return expected


def main() -> None:
    subprocess.run(["opam", "exec", "--", "dune", "build"], cwd=ROOT, check=True)

    for name, want in load_expected().items():
        path = TEST_DIR / name
        want_exit = exit_code(want)
        for opt in (False, True):
            asm = compile_source(path, opt=opt)
            (
                got,
                steps,
                dyn_ops,
                divrem_consts,
                mul_consts,
                li_profile,
            ) = run_asm(asm)
            mode = "-opt" if opt else "normal"
            print(f"{name} [{mode}]: got {got}, expected {want_exit}, steps {steps}")
            if opt:
                branch_count = sum(
                    dyn_ops[op]
                    for op in ("beqz", "bnez", "beq", "bne", "blt", "bge")
                )
                print(
                    "item10-dynamic-mix "
                    f"name={name} "
                    f"steps={steps} "
                    f"li={dyn_ops['li']} "
                    f"la={dyn_ops['la']} "
                    f"mul={dyn_ops['mul']} "
                    f"div={dyn_ops['div']} "
                    f"rem={dyn_ops['rem']} "
                    f"slli={dyn_ops['slli']} "
                    f"srli={dyn_ops['srli']} "
                    f"srai={dyn_ops['srai']} "
                    f"andi={dyn_ops['andi']} "
                    f"xor={dyn_ops['xor']} "
                    f"slti={dyn_ops['slti']} "
                    f"lw={dyn_ops['lw']} "
                    f"sw={dyn_ops['sw']} "
                    f"addi={dyn_ops['addi']} "
                    f"add={dyn_ops['add']} "
                    f"sub={dyn_ops['sub']} "
                    f"compare={dyn_ops['slt'] + dyn_ops['sltu'] + dyn_ops['sltiu'] + dyn_ops['slti'] + dyn_ops['xori']} "
                    f"branch={branch_count} "
                    f"jump={dyn_ops['j']} "
                    f"call={dyn_ops['call']} "
                    f"ret={dyn_ops['ret']}"
                )
                if divrem_consts:
                    payload = " ".join(
                        f"{kind.replace(':', '-by-')}={count}"
                        for kind, count in sorted(divrem_consts.items())
                    )
                    print(
                        "item10-divrem-const "
                        f"name={name} "
                        f"{payload}"
                    )
                if mul_consts:
                    payload = " ".join(
                        f"{kind.replace(':', '-')}={count}"
                        for kind, count in sorted(mul_consts.items())
                    )
                    print(
                        "item10-mul-const "
                        f"name={name} "
                        f"{payload}"
                    )
                if li_profile:
                    payload = " ".join(
                        f"v{key.replace(':', '-next-')}={count}"
                        for key, count in sorted(li_profile.items())
                    )
                    print(
                        "item10-li-profile "
                        f"name={name} "
                        f"{payload}"
                    )
            if got != want_exit:
                raise RuntimeError(
                    f"{name} [{mode}] returned {got}, expected {want_exit} "
                    f"(raw expected {want})"
                )

    invalid_dir = TEST_DIR / "invalid"
    for path in sorted(invalid_dir.glob("*.tc")):
        compile_expect_failure(path)
        print(f"{path.name} [invalid]: rejected")


if __name__ == "__main__":
    main()
