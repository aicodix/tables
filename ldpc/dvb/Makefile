
GLPSOL = glpsol

.PHONY: info
info: $(addprefix info/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: comp
comp: $(addprefix comp/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: check
check: $(addprefix check/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: transform
transform: $(addprefix trans/,$(notdir $(wildcard orig/dvb_*.txt)))

comp/dvb_%.txt: fixed/dvb_%.txt comp_trans
	./comp_trans $< $(addprefix trans/,$(notdir $<))

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

dvb_trans: dvb_trans.cc
info_trans: info_trans.cc
comp_trans: comp_trans.cc
check_trans: check_trans.cc
check_vector: check_vector.cc
vector_trans: vector_trans.cc
model_trans: model_trans.cc
solved_trans: solved_trans.cc

.PHONY: transform_15
transform_15: $(addprefix trans_15/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: comp_15
comp_15: $(addprefix comp_15/,$(notdir $(wildcard fixed_15/dvb_*.txt)))

.PHONY: check_15
check_15: $(addprefix check_15/,$(notdir $(wildcard fixed_15/dvb_*.txt)))

.PHONY: solve_15
solve_15: $(addprefix solved_15/,$(notdir $(wildcard input_15/dvb_*.txt)))

solved_15/dvb_%.txt: input_15/dvb_%.txt | model_trans solved_trans
	mkdir -p model_15
	./model_trans $(addprefix model_15/,$(notdir $<)) $<
	mkdir -p solution_15
	$(GLPSOL) -o $(addprefix solution_15/,$(notdir $<)) --lp $(addprefix model_15/,$(notdir $<))
	rm -f $(addprefix model_15/,$(notdir $<))
	mkdir -p solved_15
	./solved_trans $@ $(addprefix solution_15/,$(notdir $<)) $(addprefix input_15/,$(notdir $<))
	rm -f $(addprefix solution_15/,$(notdir $<))

comp_15/dvb_%.txt: fixed_15/dvb_%.txt comp_trans
	./comp_trans $< $(addprefix trans_15/,$(notdir $<))

check_15/dvb_%.txt: fixed_15/dvb_%.txt check_vector
	./check_vector $<

trans_15/dvb_16200_%.txt: fixed/dvb_16200_%.txt vector_trans
	./vector_trans $@ $< 16200 360 15

trans_15/dvb_32400_%.txt: fixed/dvb_32400_%.txt vector_trans
	./vector_trans $@ $< 32400 360 15

trans_15/dvb_64800_%.txt: fixed/dvb_64800_%.txt vector_trans
	./vector_trans $@ $< 64800 360 15

.PHONY: transform_30
transform_30: $(addprefix trans_30/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: comp_30
comp_30: $(addprefix comp_30/,$(notdir $(wildcard fixed_30/dvb_*.txt)))

.PHONY: check_30
check_30: $(addprefix check_30/,$(notdir $(wildcard fixed_30/dvb_*.txt)))

.PHONY: solve_30
solve_30: $(addprefix solved_30/,$(notdir $(wildcard input_30/dvb_*.txt)))

solved_30/dvb_%.txt: input_30/dvb_%.txt | model_trans solved_trans
	mkdir -p model_30
	./model_trans $(addprefix model_30/,$(notdir $<)) $<
	mkdir -p solution_30
	$(GLPSOL) -o $(addprefix solution_30/,$(notdir $<)) --lp $(addprefix model_30/,$(notdir $<))
	rm -f $(addprefix model_30/,$(notdir $<))
	mkdir -p solved_30
	./solved_trans $@ $(addprefix solution_30/,$(notdir $<)) $(addprefix input_30/,$(notdir $<))
	rm -f $(addprefix solution_30/,$(notdir $<))

comp_30/dvb_%.txt: fixed_30/dvb_%.txt comp_trans
	./comp_trans $< $(addprefix trans_30/,$(notdir $<))

check_30/dvb_%.txt: fixed_30/dvb_%.txt check_vector
	./check_vector $<

trans_30/dvb_16200_%.txt: fixed/dvb_16200_%.txt vector_trans
	./vector_trans $@ $< 16200 360 30

trans_30/dvb_32400_%.txt: fixed/dvb_32400_%.txt vector_trans
	./vector_trans $@ $< 32400 360 30

trans_30/dvb_64800_%.txt: fixed/dvb_64800_%.txt vector_trans
	./vector_trans $@ $< 64800 360 30

.PHONY: transform_45
transform_45: $(addprefix trans_45/,$(notdir $(wildcard fixed/dvb_*.txt)))

.PHONY: comp_45
comp_45: $(addprefix comp_45/,$(notdir $(wildcard fixed_45/dvb_*.txt)))

.PHONY: check_45
check_45: $(addprefix check_45/,$(notdir $(wildcard fixed_45/dvb_*.txt)))

.PHONY: solve_45
solve_45: $(addprefix solved_45/,$(notdir $(wildcard input_45/dvb_*.txt)))

solved_45/dvb_%.txt: input_45/dvb_%.txt | model_trans solved_trans
	mkdir -p model_45
	./model_trans $(addprefix model_45/,$(notdir $<)) $<
	mkdir -p solution_45
	$(GLPSOL) -o $(addprefix solution_45/,$(notdir $<)) --lp $(addprefix model_45/,$(notdir $<))
	rm -f $(addprefix model_45/,$(notdir $<))
	mkdir -p solved_45
	./solved_trans $@ $(addprefix solution_45/,$(notdir $<)) $(addprefix input_45/,$(notdir $<))
	rm -f $(addprefix solution_45/,$(notdir $<))

comp_45/dvb_%.txt: fixed_45/dvb_%.txt comp_trans
	./comp_trans $< $(addprefix trans_45/,$(notdir $<))

check_45/dvb_%.txt: fixed_45/dvb_%.txt check_vector
	./check_vector $<

trans_45/dvb_16200_%.txt: fixed/dvb_16200_%.txt vector_trans
	./vector_trans $@ $< 16200 360 45

trans_45/dvb_32400_%.txt: fixed/dvb_32400_%.txt vector_trans
	./vector_trans $@ $< 32400 360 45

trans_45/dvb_64800_%.txt: fixed/dvb_64800_%.txt vector_trans
	./vector_trans $@ $< 64800 360 45

.PHONY: clean
clean:
	rm -rf dvb_trans info_trans comp_trans check_trans check_vector vector_trans
	rm -rf model_trans solved_trans model_15 solution_15 model_30 solution_30 model_45 solution_45

