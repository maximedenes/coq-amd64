ASM=as --64

%.bin: %.S
	$(ASM) $< -o $@

%.show: %.bin force
	objdump -d -M intel $*.bin

force:
