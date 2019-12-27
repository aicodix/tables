/*
Generate model of table that avoids data hazards

Copyright 2019 Ahmet Inan <inan@aicodix.de>
*/

#include <fstream>
#include <iostream>
#include <vector>

const int PIPELINE_LENGTH = 13;
const int MAX_DISTANCE = 16;

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
	table_model << "Maximize" << std::endl;
	for (int line = 0; line < ptys.size(); ++line) {
		for (int pty = 0; pty < ptys.size(); ++pty) {
			if (abs(pty-line) < MAX_DISTANCE) {
				int weight = ptys[line].size() == ptys[pty].size() ? 2 : 1;
				table_model << " +" << weight << "P" << pty << "L" << line;
			}
		}
	}
	table_model << std::endl;
	table_model << "Subject to" << std::endl;
	for (int line = 0; line < ptys.size(); ++line) {
		for (int pty = 0; pty < ptys.size(); ++pty)
			if (abs(pty-line) < MAX_DISTANCE)
				table_model << " +P" << pty << "L" << line;
		table_model << " <= 1" << std::endl;
	}
	for (int pty = 0; pty < ptys.size(); ++pty) {
		for (int line = 0; line < ptys.size(); ++line)
			if (abs(pty-line) < MAX_DISTANCE)
				table_model << " +P" << pty << "L" << line;
		table_model << " <= 1" << std::endl;
	}
	for (int pty0 = 0; pty0 < ptys.size(); ++pty0) {
		for (int pty1 = pty0+1; pty1 < ptys.size(); ++pty1) {
			for (const auto &loc0: ptys[pty0])
				for (const auto &loc1: ptys[pty1])
					if (loc0.off == loc1.off)
						goto found;
			continue;
			found:
			int delay0 = (PIPELINE_LENGTH + 2 * ptys[pty0].size() - 1) / ptys[pty0].size();
			for (int dist = 1; dist < delay0; ++dist)
				for (int line = 0; line < ptys.size(); ++line)
					if (abs(pty0-line) < MAX_DISTANCE && abs(pty1-(line+dist)%ptys.size()) < MAX_DISTANCE)
						table_model << "P" << pty0 << "L" << line << " + P" << pty1 << "L" << (line+dist)%ptys.size() << " <= 1" << std::endl;
			int delay1 = (PIPELINE_LENGTH + 2 * ptys[pty1].size() - 1) / ptys[pty1].size();
			for (int dist = 1; dist < delay1; ++dist)
				for (int line = 0; line < ptys.size(); ++line)
					if (abs(pty1-line) < MAX_DISTANCE && abs(pty0-(line+dist)%ptys.size()) < MAX_DISTANCE)
						table_model << "P" << pty1 << "L" << line << " + P" << pty0 << "L" << (line+dist)%ptys.size() << " <= 1" << std::endl;
		}
	}
	table_model << "Binary" << std::endl;
	for (int line = 0; line < ptys.size(); ++line) {
		for (int pty = 0; pty < ptys.size(); ++pty)
			if (abs(pty-line) < MAX_DISTANCE)
				table_model << " P" << pty << "L" << line;
		table_model << std::endl;
	}
	table_model << "End" << std::endl;
	return 0;
}
