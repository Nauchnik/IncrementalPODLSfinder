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
#include <set>
#include "odls_sequential.h"

std::vector<int> makeLiterals(dls cur_dls);
void normalizeLS(dls &cur_DLS);

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
	std::stringstream init_cnf_sstream, sstream;
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
	std::vector<odls_pair> odls_pair_vec;
	odls_sequential odls_seq;
	odls_seq.readOdlsPairs(known_podls_file_name, odls_pair_vec);
	// construct a set of unique DLSs from these pairs
	std::vector<dls> unique_dls_vec;
	std::vector<std::vector<int>> forbidden_DLS_literals_vec;
	bool isInsertRequired;

	for (auto &x : odls_pair_vec) {
		if (x.dls_1[0] != "0123456789")	{
			normalizeLS(x.dls_1);
			for (auto &y : x.dls_1) {
				for (auto &y2 : y)
					std::cout << y2 << " ";
				std::cout << std::endl;
			}
			std::cout << std::endl;
		}
		if (x.dls_2[0] != "0123456789") {
			normalizeLS(x.dls_2);
			for (auto &y : x.dls_2) {
				for (auto &y2 : y)
					std::cout << y2 << " ";
				std::cout << std::endl;
			}
			std::cout << std::endl;
		}
		isInsertRequired = true;
		for (auto &y : unique_dls_vec)
			if (y == x.dls_1) {
				isInsertRequired = false;
				break;
			}
		if (isInsertRequired) {
			unique_dls_vec.push_back(x.dls_1);
			forbidden_DLS_literals_vec.push_back(makeLiterals(x.dls_2));
		}	
		//
		isInsertRequired = true;
		for (auto &y : unique_dls_vec)
			if (y == x.dls_2) {
				isInsertRequired = false;
				break;
			}
		if (isInsertRequired) {
			unique_dls_vec.push_back(x.dls_2);
			forbidden_DLS_literals_vec.push_back(makeLiterals(x.dls_1));
		}
	}
	// make CNF for every unique DLS
	unsigned row_index, column_index;
	std::ofstream cnf_with_known_dls;
	std::string cnf_with_known_dls_name;
	std::stringstream cur_dls_clauses_sstream, forbidden_assumption_clauses_sstream, dls_comments_sstream;
	
	unsigned new_cnf_variable = cnf_var_count + 1; // an additional variable for encoding conjunction into set of clauses
	unsigned k = 0;
	for (auto &x : unique_dls_vec) {
		dls_comments_sstream << "c known DLS:" << std::endl;
		dls_comments_sstream << "c 0 1 2 3 4 5 6 7 8 9" << std::endl;
		for (row_index = 1; row_index < x.size(); row_index++) { // skip row # 0 - it if fixed already
			dls_comments_sstream << "c ";
			for (column_index = 0; column_index < x[0].size(); column_index++) {
				cur_dls_clauses_sstream << 100 * row_index + 10 * column_index + (x[row_index][column_index] - 48) + 1 << " 0\n"; // 1000*0 + ...
				dls_comments_sstream << x[row_index][column_index];
				if (column_index != x.size()-1)
					dls_comments_sstream << " ";
			}
			dls_comments_sstream << std::endl;
		}
		// construct clauses for forbidding current assumption
		// write clause A == B -> (A or not(B)) and ( not(A) or B ) where A is a new variable
		// if here B, for example, is ( x1 or (notx2) ) then A == (x1 or not(x2) ) =>
		// (A or not(x1) or x2) and (not(A) or x1) and (not(A) or not(x2))
		// the last two clauses were made with the help of distributive rule
		// equality condition clause with positive phase of the new variable
		forbidden_assumption_clauses_sstream << new_cnf_variable << " ";
		for (unsigned j = 0; j < forbidden_DLS_literals_vec[k].size(); j++)
			forbidden_assumption_clauses_sstream << "-" << forbidden_DLS_literals_vec[k][j] << " ";
		forbidden_assumption_clauses_sstream << "0" << std::endl;
		// equality condition clauses with negative phase of the new variable
		for (unsigned j = 0; j < forbidden_DLS_literals_vec[k].size(); j++) {
			forbidden_assumption_clauses_sstream << "-" << new_cnf_variable << " "; // negative phase cause De Morgana rule
			forbidden_assumption_clauses_sstream << forbidden_DLS_literals_vec[k][j] << " 0" << std::endl;
		}
		// add negative phase of the new variable - we must forbid it
		forbidden_assumption_clauses_sstream << "-" << new_cnf_variable << " 0" << std::endl;
		// write obtained clauses to a CNF
		sstream << k;
		cnf_with_known_dls_name = "PODLS_known_DLS_" + sstream.str() + ".cnf";
		cnf_with_known_dls.open(cnf_with_known_dls_name.c_str(), std::ios_base::out);
		cnf_with_known_dls << dls_comments_sstream.str();
		cnf_with_known_dls << init_cnf_sstream.str();
		cnf_with_known_dls << cur_dls_clauses_sstream.str();
		cnf_with_known_dls << forbidden_assumption_clauses_sstream.str();
		cnf_with_known_dls.close(); 
		cnf_with_known_dls.clear();
		forbidden_assumption_clauses_sstream.clear();
		forbidden_assumption_clauses_sstream.str("");
		sstream.str("");
		sstream.clear();
		dls_comments_sstream.str("");
		dls_comments_sstream.clear();
		cur_dls_clauses_sstream.clear();
		cur_dls_clauses_sstream.str("");
		k++;
	}
	
	return 0;
}

// normalize LS by 1st row
void normalizeLS(dls &cur_DLS)
{
	char ch;
	dls new_DLS;
	unsigned LS_order = cur_DLS.size();
	new_DLS.resize(cur_DLS.size());
	for (unsigned i = 0; i < LS_order; i++)
		new_DLS[i].resize(LS_order);
	for (unsigned i = 0; i < LS_order; i++) {
		ch = cur_DLS[0][i];
		for (unsigned j = 0; j < LS_order; j++)
			for (unsigned j2 = 0; j2 < LS_order; j2++) {
				if (cur_DLS[j][j2] == ch)
					new_DLS[j][j2] = '0' + i;
			}
	}
	cur_DLS = new_DLS;
}

// Only literals which correspond to 1 are to be made
std::vector<int> makeLiterals(dls cur_dls)
{
	std::vector<int> result_vec;
	unsigned row_index, column_index;
	for (row_index = 1; row_index < cur_dls.size() - 1; row_index++) { // skip row # 0 - it if fixed already
		for (column_index = 0; column_index < cur_dls[0].size() - 1; column_index++)
			result_vec.push_back( 1000 * 1 + 100 * row_index + 10 * column_index + (cur_dls[row_index][column_index] - 48) + 1 );
	}
	return result_vec;
}