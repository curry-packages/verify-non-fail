# Make different versions of the tool for different abstract domains.
# The abstract domains are defined in the modules src/Verify/Domain_...

CPMBIN=$(HOME)/.cpm/bin

.PHONY: all
all:
	$(MAKE) Domain_Values2
	$(MAKE) Domain_Values5
	$(MAKE) Domain_Values
	cp -p $(CPMBIN)/curry-calltypes-values $(CPMBIN)/curry-calltypes

# Generate executable for the given domain:
.PHONY: Domain_%
Domain_%: src/Main.curry
	cp src/Verify/Domain_$*.curry src/Verify/Domain.curry
	cypm install -x
	mv $(CPMBIN)/curry-calltypes $(CPMBIN)/curry-calltypes-$(shell echo $* | tr A-Z a-z)

