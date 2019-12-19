
GLPSOL = glpsol

.PHONY: info
info: $(addprefix info/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: check
check: $(addprefix check/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: trans
trans: $(addprefix trans/,$(notdir $(wildcard orig/dvb_*.txt)))

.PHONY: trans_15
trans_15: $(addprefix trans_15/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: check_15
check_15: $(addprefix check_15/,$(notdir $(wildcard fixed_15/dvb_*.txt)))

.PHONY: solved_15
solved_15: $(addprefix solved_15/,$(notdir $(wildcard input_15/dvb_*.txt)))

model_15/dvb_%.txt: input_15/dvb_%.txt model_trans | model_15
	./model_trans $@ $<

solution_15/dvb_%.txt: model_15/dvb_%.txt | solution_15
	$(GLPSOL) -o $@ --lp $<
	rm -f $<

solved_15/dvb_%.txt: solution_15/dvb_%.txt solved_trans
	./solved_trans $@ $< $(addprefix input_15/,$(notdir $<))
	rm -f $<

check_15/dvb_%.txt: fixed_15/dvb_%.txt check_vector
	./check_vector $<

trans/dvb_16200_%.txt: orig/dvb_16200_%.txt dvb_trans
	./dvb_trans $@ $< 16200 360

trans/dvb_32400_%.txt: orig/dvb_32400_%.txt dvb_trans
	./dvb_trans $@ $< 32400 360

trans/dvb_64800_%.txt: orig/dvb_64800_%.txt dvb_trans
	./dvb_trans $@ $< 64800 360

info/dvb_16200_%.txt: fixed/dvb_16200_%.txt info_trans
	./info_trans $< 16200 360

info/dvb_32400_%.txt: fixed/dvb_32400_%.txt info_trans
	./info_trans $< 32400 360

info/dvb_64800_%.txt: fixed/dvb_64800_%.txt info_trans
	./info_trans $< 64800 360

check/dvb_16200_%.txt: fixed/dvb_16200_%.txt check_trans
	./check_trans $< 16200 360

check/dvb_32400_%.txt: fixed/dvb_32400_%.txt check_trans
	./check_trans $< 32400 360

check/dvb_64800_%.txt: fixed/dvb_64800_%.txt check_trans
	./check_trans $< 64800 360

trans_15/dvb_16200_%.txt: fixed/dvb_16200_%.txt vector_trans
	./vector_trans $@ $< 16200 360 15

trans_15/dvb_32400_%.txt: fixed/dvb_32400_%.txt vector_trans
	./vector_trans $@ $< 32400 360 15

trans_15/dvb_64800_%.txt: fixed/dvb_64800_%.txt vector_trans
	./vector_trans $@ $< 64800 360 15

dvb_trans: dvb_trans.cc
info_trans: info_trans.cc
check_trans: check_trans.cc
check_vector: check_vector.cc
vector_trans: vector_trans.cc
model_trans: model_trans.cc
solved_trans: solved_trans.cc

model_15 solution_15:
	mkdir $@

.PHONY: clean
clean:
	rm -rf dvb_trans info_trans check_trans check_vector vector_trans model_trans solved_trans model_15 solution_15

