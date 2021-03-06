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
	std::ifstream table_solution(argv[2]);
	std::string buf;
	if (!getline(table_solution, buf)) {
		std::cerr << "EOF error!" << std::endl;
		return 1;
	}
	if (buf == "unsat") {
		std::cerr << "unsatisfiable error!" << std::endl;
		return 1;
	}
	if (buf != "sat") {
		std::cerr << "unknown error!" << std::endl;
		return 1;
	}
	std::vector<int> lines(ptys.size(), -1);
	while (getline(table_solution, buf) && buf.length() > 0) {
		size_t posP = buf.find('P');
		if (posP == std::string::npos)
			continue;
		std::string subP = buf.substr(posP+1);
		size_t nxtL;
		int pty = std::stoi(subP, &nxtL);
		int base;
		std::string subL;
		size_t posL = buf.find('#');
		if (posL == std::string::npos) {
			base = 10;
			subL = subP.substr(nxtL);
		} else if (buf[posL+1] == 'b') {
			base = 2;
			subL = buf.substr(posL+2);
		} else if (buf[posL+1] == 'x') {
			base = 16;
			subL = buf.substr(posL+2);
		} else {
			std::cerr << "parsing error!" << std::endl;
			return 1;
		}
		int line = std::stoi(subL, 0, base);
		if (pty < 0 || pty >= ptys.size() || line < 0 || line >= ptys.size()) {
			std::cerr << "range error!" << std::endl;
			return 1;
		}
		if (lines[line] != -1) {
			std::cerr << "solution error!" << std::endl;
			return 1;
		}
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
