.intel_syntax noprefix
.text
.globl _start
_start:

        # ModR/M = Mod.REG.R/M

        # RAX: REG = 000
        
        # * Mod: 00
        # ** R/M: 000
        # [RAX] = 00.000.000 = 00
        LEA RAX, [RAX]
        LEA RAX, [R8]   
        # ** R/M: 001
        # [RCX] = 00.000.001 = 01
        LEA RAX, [RCX]
        LEA RAX, [R9]
        # ** R/M: 010
        # [RDX] = 00.000.010 = 02
        LEA RAX, [RDX]
        LEA RAX, [R10]
        # ** R/M: 011
        # [RBX] = 00.000.011 = 03
        LEA RAX, [RBX]
        LEA RAX, [R11]  
        # ** R/M: 100
        # SIB = 00.000.100 = 04
        LEA RAX, [RAX*2+0x12345678]
        LEA RAX, [R8*2+0x12345678]
        # ** R/M: 101
        # RIP + disp32 = 00.000.101 = 05       
        LEA RAX, [RIP]+0x12345678
        # ** R/M: 110
        # [RSI] = 00.000.110 = 06
        LEA RAX, [RSI]
        LEA RAX, [R14]
        # ** R/M: 111
        # [RDI] = 00.000.111 = 07
        LEA RAX, [RDI]
        LEA RAX, [R15]
        
        # * Mod: 01
        # ** R/M: 000, etc.
        # [RAX]+disp8 = 01.000.000 = 40
        LEA RAX, [RAX]+0x12
        LEA RAX, [R8]+0x12
        LEA RAX, [RCX]+0x12
        LEA RAX, [R9]+0x12     
        LEA RAX, [RDX]+0x12
        LEA RAX, [R10]+0x12
        LEA RAX, [RBX]+0x12
        LEA RAX, [R11]+0x12
        LEA RAX, [RSI]+0x12
        LEA RAX, [R14]+0x12
        LEA RAX, [RDI]+0x12
        LEA RAX, [R15]+0x12
 
        # ** R/M: 100
        # [][]+disp8 = 01.000.100 = 44
        LEA RAX, [RAX][RAX*1]+0x12
        LEA RAX, [RAX][RAX*2]+0x12
        LEA RAX, [RAX][RAX*4]+0x12              
        LEA RAX, [RAX][RAX*8]+0x12
        
        # ** R/M: 101
        # [RBP] = 01.000.101 = 45
        LEA RAX, [RBP]+0x12
        LEA RAX, [R13]+0x12
        
        # * Mod: 10
        # ** R/M: 000, etc.
        # [RAX]+disp32 = 10.000.000 = 80
        LEA RAX, [RAX]+0x12345678
        LEA RAX, [R8]+0x12345678
        LEA RAX, [RCX]+0x12345678
        LEA RAX, [R9]+0x12345678
        LEA RAX, [RDX]+0x12345678
        LEA RAX, [R10]+0x12345678
        LEA RAX, [RBX]+0x12345678
        LEA RAX, [R13]+0x12345678
        LEA RAX, [RSI]+0x12345678
        LEA RAX, [R14]+0x12345678
        LEA RAX, [RDI]+0x12345678
        LEA RAX, [R15]+0x12345678
 
        # ** R/M: 100
        # [][]+disp32 = 10.000.100 = 44
        LEA RAX, [RAX][RAX*1]+0x12345678
        
        # ** R/M: 101
        # [RBP] = 10.000.101 = 85
        LEA RAX, [RBP]+0x12345678
        LEA RAX, [R13]+0x12345678

        # * Mod: 11
        # ** R/M: 000, etc.
        # RAX = 11.000.000 = C0
        MOV.s RAX, RAX
        MOV.s RAX, R10  
        MOV.s RAX, RCX
        MOV.s RAX, R9
        MOV.s RAX, RDX
        MOV.s RAX, R10
        MOV.s RAX, RBX
        MOV.s RAX, R11
        MOV.s RAX, RSP
        MOV.s RAX, R12
        MOV.s RAX, RBP
        MOV.s RAX, R13
        MOV.s RAX, RSI
        MOV.s RAX, R14        
        MOV.s RAX, RDI
        MOV.s RAX, R15        
        # Which is coded just the same as:
        MOVQ XMM0, XMM7
