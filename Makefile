SLEIGH = "E:\ghidra_11.3.1_PUBLIC\support\sleigh.bat"

.PHONY: all clean

all: data/languages/e200z425n3.sla

data/languages/e200z425n3.sla: data/languages/e200z425n3.slaspec $(wildcard data/languages/*.sinc)
	$(SLEIGH) "E:\ghidra_11.3.1_PUBLIC\Ghidra\Extensions\e200z425n3\data\languages\e200z425n3.slaspec"

clean:
	rm -f data/languages/*.sla