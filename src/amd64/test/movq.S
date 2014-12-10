.intel_syntax noprefix
.text
.globl _start
_start:
        # MOVQ xmm1,xmm2/m64
        # Opcode: F3 0F 7E
        # Operand1: ModRM:reg (w)
        # Operand2: ModRM:r/m (r)
        MOVQ XMM0, XMM1
        MOVQ XMM0, [RAX]

        # MOVQ xmm2/m64,xmm1
        # Opcode: 66 0F D6
        # Operand1: ModRM:r/m (w)
        # Operand2: ModRM:reg (r)
        MOVQ.s XMM0, XMM1
        MOVQ [RAX], XMM0
