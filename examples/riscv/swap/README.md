# RISC-V swap example

## swap program

We consider the following program which swaps the
content of two given pointers to unsigned 64-bit integers.

```c
#include <stdint.h>

void swap(uint64_t * x, uint64_t * y) {
  uint64_t a, b;
  a = * x;
  b = * y;
  if (a == b)
    return;
  * x = b;
  * y = a;
}
```

## Compile and disassemble the swap program

Compile `swap.c` as a library, producing `swap.o`:
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-gcc -std=gnu99 -Wall -fno-builtin -fno-stack-protector -march=rv64g -O1 -c -o swap.o swap.c
```

Compile `swap.c` to assembly, producing `swap.s` (optional):
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-gcc -std=gnu99 -Wall -fno-builtin -fno-stack-protector -march=rv64g -O1 -S -o swap.s swap.c
```

Disassemble `swap.o`, producing `swap.da`:
```shell
/path/to/riscv/bin/riscv64-unknown-linux-gnu-objdump -d swap.o
```

## Lifting the swap program to BIR

The following command inside SML/HOL4 lifts the disassembled code to BIR:

```sml
val _ = lift_da_and_store "swap" "swap.da" ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000));
```

Parameters to the `lift_da_and_store` function are as follows:

- `"swap"`: string representing the name of the HOL4 term that will be
 defined to be equal to the translated BIR program
- `"swap.da"`: path to the disassembled program
- `((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))`: superset of the
  addresses that contains the program code. We call this memory region
  `UnmodifiableMemory`.

See `swapScript.sml` for the source code for the HOL4 theory that performs lifting.

## BIR swap program and its properties

After lifting, the BIR program resides in the HOL4 term `bir_swap_prog`.
The program's BIR statements can be obtained by:

```sml
val blocks = (fst o listSyntax.dest_list o dest_BirProgram o snd o dest_eq o concl o EVAL) ``bir_swap_prog``;
```

Each block has a unique label (e.g., `BL_Address (Imm64 0w)`). In this
case the label is an integer, which is equal to the address of the
corresponding transpiled instruction. Labels can also be strings, for
example when the block represents internal computations of an
instruction or is generated by some program transformations (i.e. loop
unrolling). A block has an internal list of statements, which are executed
sequentially.

Finally, a block always ends with a control flow statement. In this
case, the block jumps to the next block, e.g., the block having label
`BL_Address (Imm64 4w)`. Notice that it is not possible to jump to the
middle of a block.

`bir_swap_riscv_lift_THM` is the main theorem and states that the
program has been correctly translated to BIR, and has this statement:
```sml
bir_is_lifted_prog riscv_bmr (WI_end 0w 0x1000000w) bir_swap_progbin bir_swap_prog
```

See the definition of `bir_is_lifted_prog` for what the theorem means:
```
DB.find "bir_is_lifted_prog_def";
```