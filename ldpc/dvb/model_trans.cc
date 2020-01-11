/*
Generate model of table that avoids data hazards

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <fstream>
#include <iostream>
#include <vector>

const int PIPELINE_LENGTH = 13;
const bool OVERDO = true;
const bool BITVEC = false;

int main(int argc, char **argv)
{
	if (argc != 3)
		return 1;
	std::ifstream table_input(argv[2]);
	typedef struct { int off; int shi; } Loc;
	std::vector<std::vector<Loc>> ptys;
	for (int cnt; table_input >> cnt;) {
		std::vector<Loc> pty;
		for (int num = 0; num < cnt; ++num) {
			Loc loc;
			table_input >> loc.off;
			table_input.ignore(1, ':');
			table_input >> loc.shi;
			pty.emplace_back(loc);
		}
		ptys.emplace_back(pty);
	}
	int vlen = 0;
	while ((1 << vlen) < ptys.size())
		++vlen;
	std::ofstream table_model(argv[1]);
	table_model << "(set-option :produce-models true)" << std::endl;
	if (BITVEC) {
		table_model << "(set-logic QF_BV)" << std::endl;
		table_model << "(define-fun delay ((a (_ BitVec " << vlen << ")) (b (_ BitVec " << vlen << ")) (c (_ BitVec " << vlen << ")) (d (_ BitVec " << vlen << ")) (e (_ BitVec " << vlen << ")) (f (_ BitVec " << vlen << "))) Bool" << std::endl;
		table_model << "	(ite (bvult a b)" << std::endl;
		table_model << "	(and (bvuge (bvsub b a) c) (bvule (bvsub b a) d))" << std::endl;
		table_model << "	(and (bvuge (bvsub a b) e) (bvule (bvsub a b) f))" << std::endl;
		table_model << "))" << std::endl;
		for (int pty = 0; pty < ptys.size(); ++pty)
			table_model << "(declare-const P" << pty << " (_ BitVec " << vlen << "))" << std::endl;
	} else {
		table_model << "(set-logic QF_IDL)" << std::endl;
		table_model << "(define-fun delay ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int)) Bool" << std::endl;
		table_model << "	(ite (< a b)" << std::endl;
		table_model << "	(and (>= (- b a) c) (<= (- b a) d))" << std::endl;
		table_model << "	(and (>= (- a b) e) (<= (- a b) f))" << std::endl;
		table_model << "))" << std::endl;
		for (int pty = 0; pty < ptys.size(); ++pty)
			table_model << "(declare-const P" << pty << " Int)" << std::endl;
	}
	table_model << "(assert (and" << std::endl;
	table_model << "	(distinct" << std::endl;
	for (int pty = 0; pty < ptys.size(); ++pty)
		table_model << "		P" << pty << std::endl;
	table_model << "	)" << std::endl;
	for (int pty = 0; pty < ptys.size(); ++pty) {
		int min = pty;
		while (min >= 0 && ptys[pty].size() == ptys[min].size())
			--min;
		++min;
		int max = pty;
		while (max < ptys.size() && ptys[pty].size() == ptys[max].size())
			++max;
		--max;
		if (BITVEC)
			table_model << "	(bvuge P" << pty << " (_ bv" << min << " " << vlen << ")) (bvule P" << pty << " (_ bv" << max << " " << vlen << "))" << std::endl;
		else
			table_model << "	(>= P" << pty << " " << min << ") (<= P" << pty << " " << max << ")" << std::endl;
	}
	for (int pty0 = 0; pty0 < ptys.size(); ++pty0) {
		for (int pty1 = pty0+1; pty1 < ptys.size(); ++pty1) {
			for (const auto &loc0: ptys[pty0])
				for (const auto &loc1: ptys[pty1])
					if (loc0.off == loc1.off)
						goto found;
			continue;
			found:
			int delay0 = ((1 + OVERDO) * PIPELINE_LENGTH + 2 * ptys[pty0].size() - 1) / ptys[pty0].size();
			int delay1 = ((1 + OVERDO) * PIPELINE_LENGTH + 2 * ptys[pty1].size() - 1) / ptys[pty1].size();
			if (BITVEC)
				table_model << "	(delay P" << pty0 << " P" << pty1 << " (_ bv" << delay0 << " " << vlen << ") (_ bv" << ptys.size() - delay1 << " " << vlen << ") (_ bv" << delay1 << " " << vlen << ") (_ bv" << ptys.size() - delay0 << " " << vlen << "))" << std::endl;
			else
				table_model << "	(delay P" << pty0 << " P" << pty1 << " " << delay0 << " " << ptys.size() - delay1 << " " << delay1 << " " << ptys.size() - delay0 << ")" << std::endl;
		}
	}
	table_model << "))" << std::endl;
	table_model << "(check-sat)" << std::endl;
	table_model << "(get-value (" << std::endl;
	for (int pty = 0; pty < ptys.size(); ++pty)
		table_model << "	P" << pty << std::endl;
	table_model << "))" << std::endl;
	return 0;
}
