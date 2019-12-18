/*
Transform DVB LDPC table for vector decoders

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <fstream>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <vector>

int main(int argc, char **argv)
{
	if (argc != 6)
		return 1;
	std::ifstream table_input(argv[2]);
	int CODE_SCALARS = std::stoi(argv[3]);
	int BLOCK_SCALARS = std::stoi(argv[4]);
	int VECTOR_SCALARS = std::stoi(argv[5]);
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
	std::vector<std::vector<Loc>> vecs;
	int BLOCK_VECTORS = BLOCK_SCALARS / VECTOR_SCALARS;
	for (const auto &pty: ptys) {
		for (int j = 0; j < BLOCK_VECTORS; ++j) {
			std::vector<Loc> vec;
			for (const auto &loc: pty) {
				vec.emplace_back(Loc{
					BLOCK_VECTORS * loc.off + (loc.shi + j) % BLOCK_VECTORS,
					((loc.shi + j) % BLOCK_SCALARS) / BLOCK_VECTORS
				});
			}
			vecs.emplace_back(vec);
		}
	}
	for (auto &vec: vecs)
		std::sort(vec.begin(), vec.end(), [](const Loc &a, const Loc &b){ return (a.off == b.off && a.shi < b.shi) || a.off < b.off; });
	std::stable_sort(vecs.begin(), vecs.end(), [](const std::vector<Loc> &a, const std::vector<Loc> &b){ return a.size() < b.size(); });
	std::ofstream table_output(argv[1]);
	for (const auto &vec: vecs) {
		table_output << vec.size();
		for (const auto &loc: vec)
			table_output << '\t' << loc.off << ':' << loc.shi;
		table_output << std::endl;
	}
	return 0;
}

