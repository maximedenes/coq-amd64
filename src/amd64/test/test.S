.intel_syntax noprefix
.text
.globl _start
_start:

        # TEST RAX, imm32
        # REX prefix: W (48)
        # Opcode: A9
        # Operand: 4-byte immediate
        TEST RAX, 0x12345678

        # TEST r/m64, imm32
        # REX prefix: W (48)
        # Opcode: F7
        # ModRM:reg: 0
        # Operand1: ModRM:r/m
        # Operand2: 4-byte immediate
        TEST RBX, 0x12345678
        TEST QWORD PTR [RAX], 0x12345678
        TEST QWORD PTR [RCX], 0x12345678

        # TEST r/m64, r64
        # REX prefix: W (48)
        # Opcode: 85
        # Operand1: ModRM:r/m
        # Operand2: ModRM:reg
        TEST RAX, RBX
        TEST [RAX], RBX
