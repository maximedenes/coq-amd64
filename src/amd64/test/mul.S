.intel_syntax noprefix
.text
.globl _start
_start:

        # MUL r/m64
        # REX prefix: W (48)
        # Opcode: F7
        # ModRM:reg: 4
        # Operand: ModRM:r/m
        MUL RCX
        MUL QWORD PTR [RCX]
