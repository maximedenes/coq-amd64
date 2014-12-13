.intel_syntax noprefix
.text
.globl _start
_start:
        # SHRD r/m64, r64, imm8
        # REX prefix: W (48)
        # Opcode: 0F AC
        # Operand1: ModRM:r/m (w)
        # Operand2: ModRM:reg (r)
        # Operand3: imm8
        SHRD RCX, RAX, 0x12
        SHRD [RCX], RAX, 0x12

        # SHRD r/m64, r64, CL
        # REX prefix: W (48)
        # Opcode: 0F AD
        # Operand1: ModRM:r/m (w)
        # Operand2: ModRM:reg (r)
        SHRD RCX, RAX, CL
        SHRD [RCX], RAX, CL

        
