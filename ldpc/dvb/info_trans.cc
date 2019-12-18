/*
Information about transformed table

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <algorithm>
#include <fstream>
#include <iostream>
#include <vector>

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
	int PARITY_BLOCKS = ptys.size();
	int PARITY_SCALARS = PARITY_BLOCKS * BLOCK_SCALARS;
	int MESSAGE_SCALARS = CODE_SCALARS - PARITY_SCALARS;
	auto comp_size = [](const std::vector<Loc> &a, const std::vector<Loc> &b){ return a.size() < b.size(); };
	int DEGREE_MIN = std::min_element(ptys.begin(), ptys.end(), comp_size)->size();
	int DEGREE_MAX = std::max_element(ptys.begin(), ptys.end(), comp_size)->size();
	int TOTAL_LINKS = 0;
	for (const auto &pty: ptys) {
		for (const auto &loc: pty) {
			int wdf = loc.off == CODE_BLOCKS-1 && loc.shi == BLOCK_SCALARS-1;
			TOTAL_LINKS += BLOCK_SCALARS - wdf;
		}
	}
	std::cout << "BLOCK_SCALARS = " << BLOCK_SCALARS << std::endl;
	std::cout << "CODE_SCALARS = " << CODE_SCALARS << std::endl;
	std::cout << "MESSAGE_SCALARS = " << MESSAGE_SCALARS << std::endl;
	std::cout << "PARITY_BLOCKS = " << PARITY_BLOCKS << std::endl;
	std::cout << "DEGREE_MIN = " << DEGREE_MIN << std::endl;
	std::cout << "DEGREE_MAX = " << DEGREE_MAX << std::endl;
	std::cout << "TOTAL_LINKS = " << TOTAL_LINKS << std::endl;
	return 0;
}
