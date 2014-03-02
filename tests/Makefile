BINDIR = ../newspeak-1.7/bin
C2NEWSPEAK = $(BINDIR)/c2newspeak
SIMPLEAI = $(BINDIR)/simpleai

C_FILES = $(wildcard *.c)
NPK_FILES = $(C_FILES:.c=.npk)
DOT_FILES = $(NPK_FILES:.npk=.dot)
PS_FILES = $(DOT_FILES:.dot=.ps)

%.npk: %.c
	$(C2NEWSPEAK) $< -o $@

%.dot: %.npk
	$(SIMPLEAI) $< --to-dot $@

%.ps: %.dot
	dot -Tps $< -o $@

all: $(NPK_FILES) $(C_FILES)

dot: $(DOT_FILES) $(NPK_FILES)

ps: $(PS_FILES) $(DOT_FILES)

clean:
	rm *.no *.npk *.dot *.ps *~