.intel_syntax noprefix
.text
.globl _start
_start:
        # SHLD r/m64, r64, imm8
        # REX prefix: W (48)
        # Opcode: 0F A4
        # Operand1: ModRM:r/m (w)
        # Operand2: ModRM:reg (r)
        # Operand3: imm8
        SHLD RCX, RAX, 0x12
        SHLD [RCX], RAX, 0x12

        # SHLD r/m64, r64, CL
        # REX prefix: W (48)
        # Opcode: 0F A5
        # Operand1: ModRM:r/m (w)
        # Operand2: ModRM:reg (r)
        SHLD RCX, RAX, CL
        SHLD [RCX], RAX, CL

        
