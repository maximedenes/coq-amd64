.intel_syntax noprefix
.text
.globl _start
_start:

        # RET (near)
        # Opcode: C3
        RET

        # RET imm16 (near)
        # Opcode: C2
        # Operand: 2-byte immediate
        RET 0x1234
