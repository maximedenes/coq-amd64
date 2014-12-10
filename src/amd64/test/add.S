.intel_syntax noprefix
.text
.globl _start
_start:

        # ADD RAX, imm32
        # REX prefix: W (48)
        # Opcode: 05
        # Operand: 4-byte immediate
        ADD RAX, 0x12345678

        # ADD r/m64, imm32
        # REX prefix: W (48)
        # Opcode: 81
        # ModRM:reg: 0
        # Operand1: ModRM:r/m
        # Operand2: 4-byte immediate
        ADD RBX, 0x12345678
        ADD RCX, 0x12345678
        
        # ADD r/m64, r64
        # REX prefix: W (48)
        # Opcode: 01
        # Operand1: ModRM:r/m (r,w)
        # Operand2: ModRM:reg (r)
        ADD RAX, RBX
        ADD [RAX], RBX

        # ADD r64, r/m64
        # REX prefix: W (48)
        # Opcode: 03
        # Operand1: ModRM:reg (r,w)
        # Operand2: ModRM:r/m (r)
        ADD.s RAX, RBX
        ADD RAX, [RAX]
