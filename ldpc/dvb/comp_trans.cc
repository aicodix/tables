/*
Compare if two transformed tables are identical

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <fstream>
#include <iostream>
#include <algorithm>
#include <vector>

typedef struct { int off; int shi; } Loc;

bool operator != (const Loc &a, const Loc &b)
{
	return a.off != b.off || a.shi != b.shi;
}

bool comp(const std::vector<Loc> &a, const std::vector<Loc> &b)
{
	if (a.size() < b.size())
		return true;
	if (a.size() == b.size()) {
		for (int pty = 0; pty < a.size(); ++pty) {
			if (a[pty].off < b[pty].off)
				return true;
			if (a[pty].off == b[pty].off) {
				if (a[pty].shi < b[pty].shi)
					return true;
				if (a[pty].shi == b[pty].shi)
					continue;
			}
			return false;
		}
	}
	return false;
}

int main(int argc, char **argv)
{
	if (argc != 3)
		return 1;
	std::vector<std::vector<Loc>> tables[2];
	for (int side = 0; side < 2; ++side) {
		std::ifstream table(argv[side+1]);
		std::vector<std::vector<Loc>> ptys;
		for (int cnt; table >> cnt;) {
			std::vector<Loc> pty;
			for (int num = 0; num < cnt; ++num) {
				Loc loc;
				table >> loc.off;
				table.ignore(1, ':');
				table >> loc.shi;
				pty.emplace_back(loc);
			}
			tables[side].emplace_back(pty);
		}
		for (auto &pty: tables[side])
			std::sort(pty.begin(), pty.end(), [](const Loc &a, const Loc &b){ return (a.off == b.off && a.shi < b.shi) || a.off < b.off; });

		std::sort(tables[side].begin(), tables[side].end(), comp);
	}
	if (tables[0].size() != tables[1].size()) {
		std::cerr << "tables differ in number of parity check nodes." << std::endl;
		return 1;
	}
	for (int pty = 0; pty < tables[0].size(); ++pty) {
		if (tables[0][pty].size() != tables[1][pty].size()) {
			std::cerr << "parity check nodes differ in number of degrees." << std::endl;
			return 1;
		}
		for (int loc = 0; loc < tables[0][pty].size(); ++loc) {
			if (tables[0][pty][loc] != tables[1][pty][loc]) {
				std::cerr << "parity check nodes differ in locations." << std::endl;
				return 1;
			}
		}
	}
	return 0;
}
