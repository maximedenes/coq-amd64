.intel_syntax noprefix
.text
.globl _start
_start:

        NOP
backward:
        NOP

        # JMP rel32
        # Opcode: E9
        # Operand: 4-byte code offset
        JMP backward
        JMP forward

        # JMP r/m64
        # Opcode: FF
        # ModRM:reg: 4
        # Operand: ModRM:r/m (r)
        JMP RAX
        JMP [RAX]
        
        NOP
forward: 
        NOP
