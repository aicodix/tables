/*
Check transformed vector table for data hazards

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <fstream>
#include <iostream>
#include <vector>

int main(int argc, char **argv)
{
	if (argc != 2)
		return 1;
	std::ifstream table_input(argv[1]);
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
	for (int pty = 0; pty < ptys.size(); ++pty) {
		for (int num0 = 0; num0 < ptys[pty].size(); ++num0) {
			for (int num1 = num0+1; num1 < ptys[pty].size(); ++num1) {
				if (ptys[pty][num0].off == ptys[pty][num1].off) {
					if (num0+1 == num1) {
						num0 = num1;
					} else {
						std::cout << "parity " << pty << " has nonconsecutive same location offsets " << ptys[pty][num0].off << std::endl;
						++violations;
					}
				}
			}
		}
	}
	for (int pty0 = 0; pty0 < ptys.size(); ++pty0) {
		int pty1 = (pty0 + 1) % ptys.size();
		for (const auto &loc0: ptys[pty0]) {
			for (const auto &loc1: ptys[pty1]) {
				if (loc0.off == loc1.off) {
					std::cout << "consecutive parities " << pty0 << " and " << pty1 << " have same location offset " << loc0.off << std::endl;
					++violations;
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
