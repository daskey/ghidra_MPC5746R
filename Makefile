SLEIGH = ../../../support/sleigh

.PHONY: all clean

all: data/languages/ppc_32_e200.sla

data/languages/ppc_32_e200.sla: data/languages/ppc_32_e200.slaspec $(wildcard data/languages/*.sinc)
	$(SLEIGH) data/languages/ppc_32_e200.slaspec

clean:
	rm -f data/languages/*.sla