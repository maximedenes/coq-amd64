.intel_syntax noprefix
.text
.globl _start
_start:

        # LEA r64,m
        # REX prefix: W (48)
        # Opcode: 8D
        # Operand1: ModRM:reg
        # Operand2: ModRM:m
        LEA RAX, [RSI]
        LEA RAX, [RSI + 0x1234]
        LEA RAX, [RSI + 0x1234 * 2]
