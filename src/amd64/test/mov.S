.intel_syntax noprefix
.data
data:  .byte 0xDE,0xAD,0xBE,0xEF
.text
.globl _start
_start:

        # MOV r/m8, r8
        # Opcode: 88
        # Operand1: ModRM:r/m
        # Operand2: ModRM:reg
        MOV AL, BL
        MOV AH, BL
        MOV [RAX], AL
        MOV [test], AL   # Not doing what I expect (using data segment)
        
        # MOV r/m64,r64
        # REX prefix: W (48)
        # Opcode: 89
        # Operand1: ModRM:r/m
        # Operand2: ModRM:reg
        MOV RAX, RBX
        MOV [RAX], RBX
        
        # MOV r8,r/m8
        # Opcode: 8A
        # Operand1: ModRM:reg
        # Operand2: ModRM:r/m
        MOV AL,[RAX]
        
        # MOV r64,r/m64
        # REX prefix: W (48)
        # Opcode: B8
        # Operand1: ModRM:reg
        # Operand2: ModRM:r/m
        MOV RAX,[RAX]
        MOV R8,[RAX]
        MOV RAX,[R8]   
        
        # MOV r8,imm8
        # Opcode: B0 +rb
        # Operand: imm8
        MOV AL, 0x42
        
        # MOV r64,im64
        # REX prefix: W (48)
        # Opcode: B8 +rd
        # Operand: imm64
        MOV RBX, 0x123456789ABCDEF0
        MOV R11, 0x123456789ABCDEF0
        
        # Position independent code
        # https://sourceware.org/binutils/docs/as/i386_002dMemory.html#i386_002dMemory
        MOV RAX, [rip+data] # Incorrect, not in same segment
        MOV RAX, [rip+test]
        MOV RAX, [rip+0x123]        

        # Data segment adressing?
        
test:  .byte 0xDE,0xAD,0xBE,0xEF
