.intel_syntax noprefix
.text
.globl _start
_start:    
        
        # IDIV r/m64
        # REX prefix: W (48)
        # Opcode: F7
        # ModRM:reg: 7
        # Operand: ModRM:r/m (r)
        IDIV RAX
        IDIV QWORD PTR [RAX]
