.intel_syntax noprefix
.text
.globl _start
_start:

        # SETO r/m8 (OF)
        # Opcode: 0F 90
        # Operand: ModRM:r/m
        SETO AL
        SETO AH
        SETO [RAX]

        # SETNO r/m8 (¬ OF)
        # Opcode: 0F 91
        # Operand: ModRM:r/m
        SETNO AL
        SETNO AH
        SETNO [RAX]
        
        # SETC r/m8 (CF)
        # Opcode: 0F 92
        # Operand: ModRM:r/m
        SETC AL
        SETC AH
        SETC [RAX]
        
        # SETNC r/m8 (¬ CF)
        # Opcode: 0F 93
        # Operand: ModRM:r/m
        SETNC AL
        SETNC AH
        SETNC [RAX]
        
        # SETZ r/m8 (ZF)
        # Opcode: 0F 94
        # Operand: ModRM:r/m
        SETZ AL
        SETZ AH
        SETZ [RAX]
        
        # SETNZ r/m8 (¬ ZF)
        # Opcode: 0F 95
        # Operand: ModRM:r/m
        SETNZ AL
        SETNZ AH
        SETNZ [RAX]

        # SETNA r/m8 (CF ∨ ZF)
        # Opcode: 0F 96
        # Operand: ModRM:r/m
        SETNA AL
        SETNA AH
        SETNA [RAX]
        
        # SETA r/m8  (¬ CF ∧ ¬ ZF)
        # Opcode: 0F 97
        # Operand: ModRM:r/m
        SETA AL
        SETA AH
        SETA [RAX]

        # SETS r/m8 (SF)
        # Opcode: 0F 98
        # Operand: ModRM:r/m
        SETS AL
        SETS AH
        SETS [RAX]
        
        # SETNS r/m8 (¬ SF)
        # Opcode: 0F 99
        # Operand: ModRM:r/m
        SETNS AL
        SETNS AH
        SETNS [RAX]
        
        # SETP r/m8 (PF)
        # Opcode: 0F 9A
        # Operand: ModRM:r/m
        SETP AL
        SETP AH
        SETP [RAX]
        
        # SETNP r/m8 (¬ PF)
        # Opcode: 0F 9B
        # Operand: ModRM:r/m
        SETNP AL
        SETNP AH
        SETNP [RAX]
        
        # SETL r/m8 (SF ≠ OF)
        # Opcode: 0F 9C
        # Operand: ModRM:r/m
        SETL AL
        SETL AH
        SETL [RAX]
        
        # SETNL r/m8 (SF = OF)
        # Opcode: 0F 9D
        # Operand: ModRM:r/m
        SETNL AL
        SETNL AH
        SETNL [RAX]

        # SETNG r/m8 (ZF ∨ SF ≠ OF)
        # Opcode: 0F 9E
        # Operand: ModRM:r/m
        SETNG AL
        SETNG AH
        SETNG [RAX]
        
        # SETG r/m8 (¬ ZF ∧ ¬ SF)
        # Opcode: 0F 9F
        # Operand: ModRM:r/m
        SETG AL
        SETG AH
        SETG [RAX]
