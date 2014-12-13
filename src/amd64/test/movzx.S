.intel_syntax noprefix
.text
.globl _start
_start:

        # MOVZX r64, r/m8
        # REX prefix: W (48)
        # Opcode: 0F B6
        # Operand1: ModRM:reg (w)
        # Operand2: ModRM:r/m (r)
        # (Careful: AH, BH, CH, DH cannot be addressed)
        MOVZX RAX, AL
        MOVZX RAX, BYTE PTR [RAX]


