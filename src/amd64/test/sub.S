.intel_syntax noprefix
.text
.globl _start
_start:

        # SUB RAX, imm32
        # REX prefix: W (48)
        # Opcode: 2D
        # Operand: 4-byte immediate
        SUB RAX, 0x12345678

        # SUB r/m64, imm32
        # REX prefix: W (48)
        # Opcode: 81
        # ModRM:reg: 5
        # Operand1: ModRM:r/m
        # Operand2: 4-byte immediate
        SUB RBX, 0x12345678
        SUB RCX, 0x12345678
        
        # SUB r/m64, r64
        # REX prefix: W (48)
        # Opcode: 29
        # Operand1: ModRM:r/m (r,w)
        # Operand2: ModRM:reg (r)
        SUB RAX, RBX
        SUB [RAX], RBX

        # SUB r64, r/m64
        # REX prefix: W (48)
        # Opcode: 2B
        # Operand1: ModRM:reg (r,w)
        # Operand2: ModRM:r/m (r)
        SUB.s RAX, RBX
        SUB RAX, [RAX]
