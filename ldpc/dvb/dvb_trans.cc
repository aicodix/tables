/*
Transform DVB LDPC table

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <fstream>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <vector>

int main(int argc, char **argv)
{
	if (argc != 5)
		return 1;
	std::ifstream table_input(argv[2]);
	int CODE_SCALARS = std::stoi(argv[3]);
	int BLOCK_SCALARS = std::stoi(argv[4]);
	std::vector<std::vector<int>> rows;
	std::string buf;
	while (getline(table_input, buf)) {
		std::istringstream iss(buf);
		std::vector<int> cols;
		int num;
		while (iss >> num)
			cols.emplace_back(num);
		rows.emplace_back(cols);
	}
	int MESSAGE_BLOCKS = rows.size();
	int CODE_BLOCKS = CODE_SCALARS / BLOCK_SCALARS;
	int PARITY_BLOCKS = CODE_BLOCKS - MESSAGE_BLOCKS;
	int bit_pos = 0;
	typedef struct { int off; int shi; } Loc;
	std::vector<std::vector<Loc>> ptys(PARITY_BLOCKS);
	for (const auto &row: rows) {
		for (const auto &col: row) {
			int n = col % PARITY_BLOCKS;
			int m = col / PARITY_BLOCKS;
			int scalar_offset = bit_pos + (BLOCK_SCALARS - m) % BLOCK_SCALARS;
			int block_shift = scalar_offset % BLOCK_SCALARS;
			int block_offset = scalar_offset / BLOCK_SCALARS;
			ptys[n].emplace_back(Loc{block_offset, block_shift});
		}
		bit_pos += BLOCK_SCALARS;
	}
	for (int n = 0; n < PARITY_BLOCKS; ++n) {
		if (n)
			ptys[n].emplace_back(Loc{MESSAGE_BLOCKS + (n - 1), 0});
		else
			ptys[n].emplace_back(Loc{CODE_BLOCKS - 1, BLOCK_SCALARS - 1});
		ptys[n].emplace_back(Loc{MESSAGE_BLOCKS + n, 0});
	}
	for (int n = 0; n < PARITY_BLOCKS; ++n)
		std::sort(ptys[n].begin(), ptys[n].end(), [](const Loc &a, const Loc &b){ return (a.off == b.off && a.shi < b.shi) || a.off < b.off; });
	std::stable_sort(ptys.begin(), ptys.end(), [](const std::vector<Loc> &a, const std::vector<Loc> &b){ return a.size() < b.size(); });
	std::ofstream table_output(argv[1]);
	for (const auto &pty: ptys) {
		table_output << pty.size();
		for (const auto &loc: pty)
			table_output << '\t' << loc.off << ':' << loc.shi;
		table_output << std::endl;
	}
	return 0;
}

