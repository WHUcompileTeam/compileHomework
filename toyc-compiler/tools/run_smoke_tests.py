from __future__ import annotations

import math
import re
import subprocess
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


def regname(reg: str) -> str:
    return ALIASES[reg]


def split_ops(rest: str) -> list[str]:
    return [part.strip() for part in rest.split(",")]


def parse_mem(text: str) -> tuple[int, str]:
    match = re.fullmatch(r"(-?\d+)\(([^)]+)\)", text.strip())
    if not match:
        raise ValueError(f"bad memory operand: {text}")
    return int(match.group(1)), regname(match.group(2))


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


def run_asm(asm: str, limit: int = 300_000) -> tuple[int, int]:
    text, labels, data_labels, memory = load_program(asm)
    regs = {name: 0 for name in REGS_ORDER}
    regs["sp"] = 0x100000
    regs["ra"] = -1
    pc = labels["main"]
    steps = 0

    def read(reg: str) -> int:
        name = regname(reg)
        return 0 if name == "zero" else regs[name]

    def write(reg: str, value: int) -> None:
        name = regname(reg)
        if name != "zero":
            regs[name] = i32(value)

    while pc != -1:
        if steps > limit:
            raise RuntimeError("RISC-V subset interpreter step limit exceeded")
        steps += 1
        op, args = text[pc]
        next_pc = pc + 1

        if op == "addi":
            write(args[0], read(args[1]) + int(args[2]))
        elif op == "add":
            write(args[0], read(args[1]) + read(args[2]))
        elif op == "sub":
            write(args[0], read(args[1]) - read(args[2]))
        elif op == "mul":
            write(args[0], read(args[1]) * read(args[2]))
        elif op == "div":
            a, b = read(args[1]), read(args[2])
            write(args[0], math.trunc(a / b))
        elif op == "rem":
            a, b = read(args[1]), read(args[2])
            q = math.trunc(a / b)
            write(args[0], a - q * b)
        elif op == "slt":
            write(args[0], 1 if read(args[1]) < read(args[2]) else 0)
        elif op == "sltu":
            write(args[0], 1 if u32(read(args[1])) < u32(read(args[2])) else 0)
        elif op == "sltiu":
            write(args[0], 1 if u32(read(args[1])) < int(args[2]) else 0)
        elif op == "xori":
            write(args[0], read(args[1]) ^ int(args[2]))
        elif op == "li":
            write(args[0], int(args[1]))
        elif op == "neg":
            write(args[0], -read(args[1]))
        elif op == "la":
            write(args[0], data_labels[args[1]])
        elif op == "lw":
            off, base = parse_mem(args[1])
            write(args[0], memory.get(read(base) + off, 0))
        elif op == "sw":
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

    return regs["a0"] & 0xFF, steps


def load_expected() -> dict[str, int]:
    expected: dict[str, int] = {}
    for line in (TEST_DIR / "expected.txt").read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        name, value = line.split()
        expected[name] = int(value)
    return expected


def main() -> None:
    subprocess.run(["opam", "exec", "--", "dune", "build"], cwd=ROOT, check=True)

    for name, want in load_expected().items():
        path = TEST_DIR / name
        for opt in (False, True):
            asm = compile_source(path, opt=opt)
            got, steps = run_asm(asm)
            mode = "-opt" if opt else "normal"
            print(f"{name} [{mode}]: got {got}, expected {want}, steps {steps}")
            if got != want:
                raise RuntimeError(f"{name} [{mode}] returned {got}, expected {want}")

    invalid_dir = TEST_DIR / "invalid"
    for path in sorted(invalid_dir.glob("*.tc")):
        compile_expect_failure(path)
        print(f"{path.name} [invalid]: rejected")


if __name__ == "__main__":
    main()
