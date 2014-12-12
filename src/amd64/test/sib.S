.intel_syntax noprefix
.text
.globl _start
_start:

        # ModR/M = Mod.REG.R/M
        # SIB    = Scale.Index.Base

        # RAX: REG = 000
        # SIB: Mod = 00
        # SIB: R/M = 100

        # ModR/M == 00.000.100 = 04
        
        # * Scale: 1 (00)
        # [RAX][RAX*1] = 00.000.000 = 00
        # [RCX][RAX*1] = 00.000.001 = 01
        # (...)
        LEA RAX, [RAX][RAX*1]
        LEA RAX, [R8][RAX*1]        
        LEA RAX, [RCX][RAX*1]
        LEA RAX, [RDX][RAX*1]
        LEA RAX, [RBX][RAX*1]
        LEA RAX, [RSP][RAX*1]
        LEA RAX, [RAX*1]+0x12345678
        LEA RAX, [RSI][RAX*1]
        LEA RAX, [RDI][RAX*1]

        # [RAX][RAX*1] = 00.000.000 = 00
        # [RAX][RCX*1] = 00.001.000 = 08
        # [RAX][RDX*1] = 00.010.000 = 10
        # [RAX][RBX*1] = 00.011.000 = 18
        # [RAX][RBP*1] = 00.101.000 = 28
        # [RAX][RSI*1] = 00.110.000 = 30
        # [RAX][RPI*1] = 00.111.000 = 38
        LEA RAX, [RAX][RAX*1]
        LEA RAX, [RAX][RCX*1]
        LEA RAX, [RAX][RDX*1]
        LEA RAX, [RAX][RBX*1]
        LEA RAX, [RAX][RBP*1]
        LEA RAX, [RAX][RSI*1]
        LEA RAX, [RAX][RDI*1]               
        # Invalid: [RAX][RSP*1] = 00.100.000 = 20
        # Invalid: [RBX][RSP*1] = 00.100.000 = 21
        # (..)
        # Codes: [RAX][0*1] ~ [RAX]
        
        # For all registers, gas will directly code reg1,[reg2] 
	# through the reg/mem, at the exception of reg1,[RSP] (which
	# address serves to indicate a SIB)        
        LEA RAX, [RSP]
        # You might think that it's the same for RBP: no, gas will code
        #    LEA RAX, [RBP]
        # as
        #    LEA RAX, [RBP]+0x0

        # * Scale: 2 (01)
        # [RAX][RCX*2] = 01.000.000 = 40
        LEA RAX, [RCX][RAX*2]

        # * Scale: 4 (10)
        # [RAX][RCX*4] = 10.000.000 = 80
        LEA RAX, [RCX][RAX*4]

        # * Scale: 8 (11)
        # [RAX][RCX*4] = 11.000.000 = C0
        LEA RAX, [RCX][RAX*8]
