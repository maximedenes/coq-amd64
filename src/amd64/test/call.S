.intel_syntax noprefix
.text
.globl _start
_start:
        
        # CALL rel32
        # Opcode: E8
        # Operand: ModRM:r/m
backward:
        CALL forward
        CALL backward

        # CALL r/m64
        # Opcode: FF
        # ModRM:reg: 2
        # Operand: ModRM:r/m
forward:        
        CALL RAX
        CALL [RAX]
        
