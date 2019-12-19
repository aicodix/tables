/*
Generate data hazard free table from transformed table and solution

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
	std::ifstream table_input(argv[3]);
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
	std::vector<int> lines(ptys.size(), -1);
	std::ifstream table_solution(argv[2]);
	std::string buf;
	while (getline(table_solution, buf) && buf.find("Column name") == std::string::npos);
	if (!getline(table_solution, buf) || buf[0] != '-') {
		std::cerr << "EOF or parsing error!" << std::endl;
		return 1;
	}
	while (getline(table_solution, buf) && buf.length() > 0) {
		size_t P = buf.find('P');
		size_t V = buf.find('*');
		if (P == std::string::npos || V == std::string::npos) {
			std::cerr << "parsing error!" << std::endl;
			return 1;
		}
		std::string subP = buf.substr(P+1);
		size_t L;
		int pty = std::stoi(subP, &L);
		std::string subL = subP.substr(L+1);
		int line = std::stoi(subL);
		std::string subV = buf.substr(V+1);
		int val = std::stoi(subV);
		if (pty < 0 || pty >= ptys.size() || line < 0 || line >= ptys.size() || val < 0 || val > 1) {
			std::cerr << "parsing or bound error!" << std::endl;
			return 1;
		}
		if (val && lines[line] != -1) {
			std::cerr << "solution error!" << std::endl;
			return 1;
		}
		if (val)
			lines[line] = pty;
	}
	if (std::find(lines.begin(), lines.end(), -1) != lines.end()) {
		std::cerr << "no solution found!" << std::endl;
		return 1;
	}
	std::ofstream table_output(argv[1]);
	for (const auto &pty: lines) {
		table_output << ptys[pty].size();
		for (const auto &loc: ptys[pty])
			table_output << '\t' << loc.off << ':' << loc.shi;
		table_output << std::endl;
	}
	return 0;
}
