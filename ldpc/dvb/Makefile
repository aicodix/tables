
.PHONY: test
test: $(addprefix check/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: all
all: $(addprefix trans/,$(notdir $(wildcard orig/dvb_*.txt)))

trans/dvb_16200_%.txt: orig/dvb_16200_%.txt dvb_trans
	./dvb_trans $@ $< 16200 360

trans/dvb_32400_%.txt: orig/dvb_32400_%.txt dvb_trans
	./dvb_trans $@ $< 32400 360

trans/dvb_64800_%.txt: orig/dvb_64800_%.txt dvb_trans
	./dvb_trans $@ $< 64800 360

check/dvb_16200_%.txt: fixed/dvb_16200_%.txt check_trans | check
	./check_trans $< 16200 360 && touch $@

check/dvb_32400_%.txt: fixed/dvb_32400_%.txt check_trans | check
	./check_trans $< 32400 360 && touch $@

check/dvb_64800_%.txt: fixed/dvb_64800_%.txt check_trans | check
	./check_trans $< 64800 360 && touch $@

dvb_trans: dvb_trans.cc

check_trans: check_trans.cc

check:
	mkdir $@

.PHONY: clean
clean:
	rm -rf dvb_trans check_trans check

