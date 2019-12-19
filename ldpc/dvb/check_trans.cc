/*
Check transformed table for data hazards

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <fstream>
#include <iostream>
#include <vector>

const int PIPELINE_LENGTH = 7;

int main(int argc, char **argv)
{
	if (argc != 4)
		return 1;
	std::ifstream table_input(argv[1]);
	int CODE_SCALARS = std::stoi(argv[2]);
	int BLOCK_SCALARS = std::stoi(argv[3]);
	int CODE_BLOCKS = CODE_SCALARS / BLOCK_SCALARS;
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
	int violations = 0;
	for (int pty0 = 0; pty0 < ptys.size(); ++pty0) {
		int pty1 = (pty0 + 1) % ptys.size();
		int delay = (PIPELINE_LENGTH + 2 * ptys[pty0].size() - 1) / ptys[pty0].size();
		for (int end0 = BLOCK_SCALARS-delay; end0 < BLOCK_SCALARS; ++end0) {
			for (int beg1 = 0; beg1 < delay; ++beg1) {
				for (const auto &loc0: ptys[pty0]) {
					for (const auto &loc1: ptys[pty1]) {
						int wdf = loc1.off == CODE_BLOCKS-1 && loc1.shi == BLOCK_SCALARS-1;
						int shi0 = (loc0.shi+end0)%BLOCK_SCALARS;
						int shi1 = (loc1.shi+beg1)%BLOCK_SCALARS;
						if (!wdf && loc0.off == loc1.off && shi0 == shi1) {
							std::cout << "consecutive parities " << pty0 << " at " << end0 << " and " << pty1 << " at " << beg1 << " have same location shift " << loc0.shi << " at block offset " << loc0.off << std::endl;
							++violations;
						}
					}
				}
			}
		}
	}
	if (violations)
		std::cout << violations;
	else
		std::cout << "no";
	std::cout << " violations detected." << std::endl;
	return !!violations;
}
