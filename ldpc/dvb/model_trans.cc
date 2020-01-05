/*
Generate model of table that avoids data hazards

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <fstream>
#include <iostream>
#include <vector>

const int PIPELINE_LENGTH = 13;
const bool OVERDO = true;

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
	std::ofstream table_model(argv[1]);
	table_model << "(define-fun delay ((a Int) (b Int) (c Int) (d Int)) Bool" << std::endl;
	table_model << "	(if (< a b)" << std::endl;
	table_model << "	(and (>= (- b a) c) (>= (- " << ptys.size() << " (- b a)) d))" << std::endl;
	table_model << "	(and (>= (- a b) d) (>= (- " << ptys.size() << " (- a b)) c))" << std::endl;
	table_model << "))" << std::endl;
	for (int pty = 0; pty < ptys.size(); ++pty)
		table_model << "(declare-const P" << pty << " Int)" << std::endl;
	table_model << "(assert (and" << std::endl;
	table_model << "	(distinct" << std::endl;
	for (int pty = 0; pty < ptys.size(); ++pty)
		table_model << "		P" << pty << std::endl;
	table_model << "	)" << std::endl;
	for (int pty = 0; pty < ptys.size(); ++pty) {
		int min = pty;
		while (min >= 0 && ptys[pty].size() == ptys[min].size())
			--min;
		int max = pty;
		while (max < ptys.size() && ptys[pty].size() == ptys[max].size())
			++max;
		table_model << "	(> P" << pty << " " << min << ") (< P" << pty << " " << max << ")" << std::endl;
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
			table_model << "	(delay P" << pty0 << " P" << pty1 << " " << delay0 << " " << delay1 << ")" << std::endl;
		}
	}
	table_model << "))" << std::endl;
	table_model << "(check-sat)" << std::endl;
	for (int pty = 0; pty < ptys.size(); ++pty)
		table_model << "(eval P" << pty << ")" << std::endl;
	return 0;
}
