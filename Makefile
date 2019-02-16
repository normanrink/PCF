
IDRIS=idris
OPT=-O3
TESTDIR=test
BINDIR=bin

$(BINDIR)/%.typed: $(TESTDIR)/%.idr
	@$(IDRIS) -o $@ $< $(OPT) -i typed/src

$(BINDIR)/%.total: $(TESTDIR)/%.idr
	@$(IDRIS) -o $@ $< $(OPT) -i total/src

$(BINDIR)/%.untyped: $(TESTDIR)/%.idr
	@$(IDRIS) -o $@ $< $(OPT) -i total/src

.PHONY: mul fact clean

all: mul fact

mul:	$(BINDIR)/St-Mul.typed     \
	$(BINDIR)/St-Mul.total     \
	$(BINDIR)/St-Mul.untyped   \
	$(BINDIR)/BSt-Mul.typed    \
	$(BINDIR)/BSt-Mul.total    \
	$(BINDIR)/BSt-Mul.untyped  \
	$(BINDIR)/Eval-Mul.typed   \
	$(BINDIR)/Eval-Mul.total   \
	$(BINDIR)/Eval-Mul.untyped \
	$(BINDIR)/Env-Mul.total

fact:	$(BINDIR)/St-Fact.typed     \
	$(BINDIR)/St-Fact.total     \
	$(BINDIR)/St-Fact.untyped   \
	$(BINDIR)/BSt-Fact.typed    \
	$(BINDIR)/BSt-Fact.total    \
	$(BINDIR)/BSt-Fact.untyped  \
	$(BINDIR)/Eval-Fact.typed   \
	$(BINDIR)/Eval-Fact.total   \
	$(BINDIR)/Eval-Fact.untyped \
	$(BINDIR)/Env-Fact.total

clean:
	rm -rf $(BINDIR)
	rm -f $(TESTDIR)/*.ibc

$(shell mkdir -p $(BINDIR))
