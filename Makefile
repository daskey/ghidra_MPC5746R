SLEIGH = ../../../support/sleigh

.PHONY: all clean

all: data/languages/ppc_32_vle_mpc5746r

data/languages/MPC5746R_VLE.sla: data/languages/MPC5746R_VLE.slaspec $(wildcard data/languages/*.sinc)
	$(SLEIGH) data/languages/MPC5746R_VLE.slaspec

clean:
	rm -r data/languages/*.sla