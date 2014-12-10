.intel_syntax noprefix
.text
.globl _start
_start:    
        
        # IMUL r/m64
        # REX prefix: W (48)
        # Opcode: F7
        # ModRM:reg: 5
        # Operand: ModRM:r/m (r)
        IMUL RCX
        IMUL QWORD PTR [RCX]

        # IMUL r64, r/m64
        # REX prefix: W (48)
        # Opcode: 0F AF
        # Operand1: ModRM:reg (r,w)
        # Operand2: ModRM:r/m (r)
        IMUL RAX, RBX
        IMUL RAX, [RBX]

        # IMUL r64, r/m64, imm32
        # REX prefix: W (48)
        # Opcode: 69
        # Operand1: ModRM:reg (r,w)
        # Operand2: ModRM:r/m (r)
        # Operand3: imm32
        IMUL RAX, RBX, 0x12345689
        IMUL RAX, [RBX], 0x12345689
