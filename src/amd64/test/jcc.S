.intel_syntax noprefix
.text
.globl _start
_start:

        NOP
backward:
        NOP

        # JO rel32 (OF)
        # Opcode: 0F 80
        # Operand: 4-byte immediate
        JO.d32 backward
        JO.d32 forward

        # JNO rel32 (¬ OF)
        # Opcode: 0F 81
        # Operand: 4-byte immediate
        JNO.d32 backward
        JNO.d32 forward
        
        # JC rel32 (CF)
        # Opcode: 0F 82
        # Operand: 4-byte immediate
        JC.d32 backward
        JC.d32 forward
        
        # JNC rel32    (¬ CF)
        # Opcode: 0F 83
        # Operand: 4-byte immediate
        JNC.d32 backward
        JNC.d32 forward

        # JZ rel32 (ZF)
        # Opcode: 0F 84
        # Operand: 4-byte immediate
        JZ.d32 backward
        JZ.d32 forward

        # JNZ rel32 (¬ ZF)
        # Opcode: 0F 85
        # Operand: 4-byte immediate
        JNZ.d32 backward
        JNZ.d32 forward

        # JNA rel32 (CF ∨ ZF)
        # Opcode: 0F 86
        # Operand: 4-byte immediate
        JNA.d32 backward
        JNA.d32 forward

        # JA rel32    (¬ CF ∧ ¬ ZF)
        # Opcode: 0F 87
        # Operand: 4-byte immediate
        JA.d32 backward
        JA.d32 forward

        # JS rel32 (SF)
        # Opcode: 0F 88
        # Operand: 4-byte immediate
        JS.d32 backward
        JS.d32 forward
        
        # JNS rel32 (¬ SF)
        # Opcode: 0F 89
        # Operand: 4-byte immediate
        JNS.d32 backward
        JNS.d32 forward

        # JP rel32 (PF)
        # Opcode: 0F 8A
        # Operand: 4-byte immediate
        JP.d32 backward
        JP.d32 forward
        
        # JNP rel32 (¬ PF)
        # Opcode: 0F 8B
        # Operand: 4-byte immediate
        JNP.d32 backward
        JNP.d32 forward
        
        # JL rel32 (SF ≠ OF)
        # Opcode: 0F 8C
        # Operand: 4-byte immediate
        JL.d32 backward
        JL.d32 forward

        # JNL rel32 (SF = OF)
        # Opcode: 0F 8D
        # Operand: 4-byte immediate
        JNL.d32 backward
        JNL.d32 forward

        # JNG rel32 (ZF ∨ SF ≠ OF)
        # Opcode: 0F 8E
        # Operand: 4-byte immediate
        JNG.d32 backward
        JNG.d32 forward

        # JG rel32 (¬ ZF ∧ ¬ SF)
        # Opcode: 0F 8F
        # Operand: 4-byte immediate
        JG.d32 backward
        JG.d32 forward

        NOP
forward: 
        NOP
