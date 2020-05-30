
IDRIS=idris
OPT=-O3
TESTDIR=test
BINDIR=bin

TYPEDDIR=typed
TOTALDIR=total
UNTYPEDDIR=untyped
CONVENTIONALDIR=conventional
CODATADIR=codata
TOTALITYDIR=totality


.PHONY: mul fact codata totality clean purge

all: mul fact codata totality


$(TYPEDDIR)/src/PCF.ibc:
	@pushd $(TYPEDDIR) ; $(IDRIS) --build typed.ipkg ; popd

$(TOTALDIR)/src/PCF.ibc:
	@pushd $(TOTALDIR) ; $(IDRIS) --build total.ipkg ; popd

$(UNTYPEDDIR)/src/PCF.ibc:
	@pushd $(UNTYPEDDIR) ; $(IDRIS) --build untyped.ipkg ; popd

$(CONVENTIONALDIR)/src/PCF.ibc:
	@pushd $(CONVENTIONALDIR) ; $(IDRIS) --build conventional.ipkg ; popd

codata:
	@pushd $(CODATADIR) ; $(IDRIS) --build codata.ipkg ; popd

totality:
	@pushd $(TOTALITYDIR) ; $(IDRIS) --build totality.ipkg ; popd


$(BINDIR)/typed/%: $(TESTDIR)/%.idr $(TYPEDDIR)/src/PCF.ibc
	@$(IDRIS) --ibcsubdir $(BINDIR)/typed -o $@ $< $(OPT) -i $(TYPEDDIR)/src

$(BINDIR)/total/%: $(TESTDIR)/%.idr $(TOTALDIR)/src/PCF.ibc
	@$(IDRIS) --ibcsubdir $(BINDIR)/total -o $@ $< $(OPT) -i $(TOTALDIR)/src

$(BINDIR)/untyped/%: $(TESTDIR)/%.idr $(UNTYPEDDIR)/src/PCF.ibc
	@$(IDRIS) --ibcsubdir $(BINDIR)/untyped -o $@ $< $(OPT) -i $(UNTYPEDDIR)/src

$(BINDIR)/conventional/%: $(TESTDIR)/%.idr $(CONVENTIONALDIR)/src/PCF.ibc
	@$(IDRIS) --ibcsubdir $(BINDIR)/conventional -o $@ $< $(OPT) -i $(CONVENTIONALDIR)/src


mul:	$(BINDIR)/typed/St-Mul     \
	$(BINDIR)/total/St-Mul     \
	$(BINDIR)/untyped/St-Mul   \
	$(BINDIR)/conventional/St-Mul   \
	$(BINDIR)/typed/BSt-Mul    \
	$(BINDIR)/total/BSt-Mul    \
	$(BINDIR)/untyped/BSt-Mul  \
	$(BINDIR)/conventional/BSt-Mul  \
	$(BINDIR)/typed/Eval-Mul   \
	$(BINDIR)/total/Eval-Mul   \
	$(BINDIR)/untyped/Eval-Mul \
	$(BINDIR)/conventional/Eval-Mul \
	$(BINDIR)/total/Env-Mul

fact:	$(BINDIR)/typed/St-Fact     \
	$(BINDIR)/total/St-Fact     \
	$(BINDIR)/untyped/St-Fact   \
	$(BINDIR)/conventional/St-Fact   \
	$(BINDIR)/typed/BSt-Fact    \
	$(BINDIR)/total/BSt-Fact    \
	$(BINDIR)/untyped/BSt-Fact  \
	$(BINDIR)/conventional/BSt-Fact  \
	$(BINDIR)/typed/Eval-Fact   \
	$(BINDIR)/total/Eval-Fact   \
	$(BINDIR)/untyped/Eval-Fact \
	$(BINDIR)/conventional/Eval-Fact \
	$(BINDIR)/total/Env-Fact

clean:
	rm -rf $(BINDIR)

purge: clean
	cd $(TYPEDDIR)        ; $(IDRIS) --clean typed.ipkg        ; cd -
	cd $(TOTALDIR)        ; $(IDRIS) --clean total.ipkg        ; cd -
	cd $(UNTYPEDDIR)      ; $(IDRIS) --clean untyped.ipkg      ; cd -
	cd $(CONVENTIONALDIR) ; $(IDRIS) --clean conventional.ipkg ; cd -
	cd $(CODATADIR)       ; $(IDRIS) --clean codata.ipkg       ; cd -
	cd $(TOTALITYDIR)     ; $(IDRIS) --clean totality.ipkg     ; cd -

$(shell mkdir -p $(BINDIR))
$(shell mkdir -p $(BINDIR)/typed)
$(shell mkdir -p $(BINDIR)/total)
$(shell mkdir -p $(BINDIR)/untyped)
$(shell mkdir -p $(BINDIR)/conventional)
$(shell mkdir -p $(BINDIR)/codata)
$(shell mkdir -p $(BINDIR)/totality)
