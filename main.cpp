/*
Program for searching pairs of orthogonal diagonal Latin squares (PODLS) of order 10.
On the first stage to the CNF that encodes problem of searching for a PODLS of order 10 
we add inforamtion about all known DLS of order 10 for which at least one PODLS of order 10 exists.
As a result for all such DLSs own CNF is constructed. The goal is to find for every such CNF all possible PODLS.
*/

#include <iostream>
#include <string>
#include <sstream>
#include <fstream>
#include <vector>
#include <ctime>
#include "../pdsat/src_common/latin_squares.h"

std::vector<int> makeLiterals(dls cur_dls);
unsigned processDLS(unsigned cnf_var_count, std::stringstream &init_cnf_sstream, dls cur_dls);
dls getDLSfromSolutionFile(std::string solutionfile_name);

int main( int argc, char **argv )
{
#ifdef _DEBUG
	argc = 3;
	argv[1] = "D:/Tests/ferrumsat/Latin Square encodings/ls10_2_diag.cnf";
	argv[2] = "D:/Programming/pdsat/src_common/ODLS_10_pairs.txt";
#endif
	
	if (argc != 3) {
		std::cerr << "Usage: [CNF that encodes the problem of search for PODLS of order 10] [file with known PODLS]";
		return 1;
	}
	
	// read CNF that encodes the problem of search for PODLS of order 10
	std::string init_cnf_file_name = argv[1];
	std::ifstream init_cnf_file(init_cnf_file_name.c_str());
	if (!init_cnf_file.is_open()) {
		std::cerr << "file " << init_cnf_file_name << " wasn't open" << std::endl;
		return 1;
	}
	std::stringstream sstream, init_cnf_sstream;
	std::string str;
	unsigned cnf_var_count = 0;
	while (getline(init_cnf_file, str)) {
		init_cnf_sstream << str << std::endl;
		if ( str.find("p cnf ") != std::string::npos ) {
			sstream << str;
			sstream >> str;
			sstream >> str;
			sstream >> cnf_var_count;
			sstream.str("");
			sstream.clear();
		}
	}
	init_cnf_file.close();
	if (cnf_var_count == 0) {
		std::cerr << "cnf_var_count " << cnf_var_count << std::endl;
		return 1;
	}
	
	// read all known PODLS of order 10
	std::string known_podls_file_name = argv[2];
	latin_square ls;
	ls.readOdlsPairs(known_podls_file_name);
	// construct a set of unique DLSs from these pairs
	std::vector<dls> unique_dls_vec;

	// get unique DLSs from the known pairs of ODLS
	unique_dls_vec = getSetUniqueDLS(odls_seq.odls_pair_vec );
	std::vector<unsigned> sat_count_vec;
	sat_count_vec.resize(unique_dls_vec.size());
	
	unsigned k = 0;
	for (auto &x : unique_dls_vec)
		sat_count_vec[k++] = processDLS(cnf_var_count, init_cnf_sstream, x);
	
	k = 0;
	std::cout << "final sat count" << std::endl;
	for (auto &x : sat_count_vec)
		std::cout << "sat count for DLS # " << k++ << " " << x << std::endl;
	
	return 0;
}

unsigned processDLS(unsigned cnf_var_count, std::stringstream &init_cnf_sstream, dls cur_dls)
{
	// make CNF for every unique DLS
	unsigned row_index, column_index;
	std::ofstream cnf_with_known_dls;
	std::ifstream out_incremental_file;
	std::vector<int> forbidden_DLS_literals;
	
	std::stringstream cur_dls_clauses_sstream, forbidden_assumption_clauses_sstream, dls_comments_sstream;
	unsigned new_cnf_variable;
	bool isSATfound = false;
	new_cnf_variable = cnf_var_count;
	std::string cnf_with_known_dls_name = "PODLS_known_DLS_tmp.cnf";
	std::string out_incremental_file_name = "PODLS_tmp.out";
	std::string system_str;
	dls dls_from_output;
	unsigned sat_count = 0;

	std::cout << "---" << std::endl;
	
	dls_comments_sstream << "c 0 1 2 3 4 5 6 7 8 9" << std::endl;
	for (row_index = 1; row_index < cur_dls.size(); row_index++) { // skip row # 0 - it if fixed already
		dls_comments_sstream << "c ";
		for (column_index = 0; column_index < cur_dls[0].size(); column_index++) {
			cur_dls_clauses_sstream << 100 * row_index + 10 * column_index + (cur_dls[row_index][column_index] - 48) + 1 << " 0\n"; // 1000*0 + ...
			dls_comments_sstream << cur_dls[row_index][column_index];
			if (column_index != cur_dls.size() - 1)
				dls_comments_sstream << " ";
		}
		dls_comments_sstream << std::endl;
	}
	
	for (;;)
	{ // incremental iterations for finding all SAT assignments of the CNF
		new_cnf_variable++; // an additional variable for encoding conjunction into set of clauses
		
		// write obtained clauses to a CNF
		cnf_with_known_dls.open(cnf_with_known_dls_name.c_str(), std::ios_base::out);
		cnf_with_known_dls << dls_comments_sstream.str();
		cnf_with_known_dls << init_cnf_sstream.str();
		cnf_with_known_dls << cur_dls_clauses_sstream.str();
		// first time forbidden_assumption_clauses_sstream is empty
		cnf_with_known_dls << forbidden_assumption_clauses_sstream.str();
		cnf_with_known_dls.clear();
		cnf_with_known_dls.close();
		
		// fix CNF
		system_str = "./fix_cnf " + cnf_with_known_dls_name;
		std::cout << "system_str " << system_str << std::endl;
		system(system_str.c_str());
		// launch SAT solver
		system_str = "./plingeling " + cnf_with_known_dls_name + " &> " + out_incremental_file_name;
		std::cout << "system_str " << system_str << std::endl;
		system(system_str.c_str());
		// read output of a SAT solver
		dls_from_output = getDLSfromSolutionFile(out_incremental_file_name);
		printDLS(dls_from_output);
		isSATfound = (dls_from_output.size() > 0) ? true : false;
		if (!isSATfound) {
			std::cout << "UNSAT" << std::endl;
			break;
		}
		sat_count++;
		std::cout << "current sat_count " << sat_count << std::endl;
		forbidden_DLS_literals = makeLiterals(dls_from_output);
		std::cout << "forbidden_DLS_literals.size() " << forbidden_DLS_literals.size() << std::endl;

		// construct clauses for forbidding current assumption
		// write clause A == B -> (A or not(B)) and ( not(A) or B ) where A is a new variable
		// if here B, for example, is ( x1 or (notx2) ) then A == (x1 or not(x2) ) =>
		// (A or not(x1) or x2) and (not(A) or x1) and (not(A) or not(x2))
		// the last two clauses were made with the help of distributive rule
		// equality condition clause with positive phase of the new variable
		forbidden_assumption_clauses_sstream << new_cnf_variable << " ";
		for (unsigned j = 0; j < forbidden_DLS_literals.size(); j++)
			forbidden_assumption_clauses_sstream << "-" << forbidden_DLS_literals[j] << " ";
		forbidden_assumption_clauses_sstream << "0" << std::endl;
		// equality condition clauses with negative phase of the new variable
		for (unsigned j = 0; j < forbidden_DLS_literals.size(); j++) {
			forbidden_assumption_clauses_sstream << "-" << new_cnf_variable << " "; // negative phase cause De Morgana rule
			forbidden_assumption_clauses_sstream << forbidden_DLS_literals[j] << " 0" << std::endl;
		}
		// add negative phase of the new variable - we must forbid it
		forbidden_assumption_clauses_sstream << "-" << new_cnf_variable << " 0" << std::endl;
		// don't clear forbidden_assumption_clauses_sstream, we need to increment it every iteration
		forbidden_DLS_literals.clear();
	}
	std:: cout << "final sat_count " << sat_count << std::endl;
	return sat_count;
}

dls getDLSfromSolutionFile( std::string solutionfile_name)
{
	// check solution
	std::stringstream sstream;
	std::ifstream solutionfile(solutionfile_name.c_str(), std::ios_base::in);
	std::string str;
	dls new_dls;
	std::string dls_row;
	int val;

	if (!solutionfile.is_open()) {
		std::cerr << "solutionfile " << solutionfile_name << " not open" << std::endl;
		exit(1);
	}
	
	while (std::getline(solutionfile, str)) {
		if ((str[0] == 'v') && (str[1] == ' ')) {
			sstream << str.substr(2);
			while (sstream >> val) {
				//if ( ( val >= 2001 ) && ( val <= 3000 ) ) { // for 3rd DLS
				if ((val >= 1001) && (val <= 2000)) {
					val = val % 10 ? (val % 10) - 1 : 9;
					dls_row.push_back('0' + val);
				}
				if (dls_row.size() == 10) {
					new_dls.push_back(dls_row);
					//std::cout << dls_row << std::endl;
					dls_row = "";
				}
			}
			sstream.clear(); sstream.str("");
		}
	}
	/*std::cout << std::endl;
	for (auto &x : new_dls) {
		for (unsigned i = 0; i<x.size(); i++)
			std::cout << x[i] << " ";
		std::cout << std::endl;
	}*/
	
	solutionfile.close();
	return new_dls;
}

void printDLS(dls cur_dls)
{
	for (unsigned i = 0; i < cur_dls.size(); i++) {
		for (unsigned j = 0; j < cur_dls[i].size(); j++) {
			std::cout << cur_dls[i][j];
			if (j != cur_dls[i].size() - 1)
				std::cout << " ";
		}
	}
}

void constructOLS()
{
	std::ifstream ifile("MayBeTriple.txt");
	std::string str, tmp_str, cur_dls_row;
	dls cur_dls;
	std::vector<dls> dls_vec;
	std::stringstream sstream;
	while (getline(ifile, str)) {
		if (str.size() < 18) continue;
		sstream << str;
		while (sstream >> tmp_str) {
			cur_dls_row += tmp_str;
			if (cur_dls_row.size() == 10) {
				cur_dls.push_back(cur_dls_row);
				cur_dls_row = "";
			}
			if (cur_dls.size() == 10) {
				dls_vec.push_back(cur_dls);
				cur_dls.clear();
			}
		}
		sstream.clear(); sstream.str("");
	}
	ifile.close();

	odls_sequential odls_seq; 
	odls_pair odls_p;
	odls_p.dls_1 = dls_vec[0];
	odls_p.dls_2 = dls_vec[1];
	odls_pseudotriple pseudotriple;
	odls_seq.makePseudotriple(odls_p, dls_vec[2], pseudotriple);
	std::cout << pseudotriple.unique_orthogonal_cells.size();
}