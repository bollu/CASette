#include "assert.h"
#include <ios>
#include <vector>
#include <algorithm>
#include <iostream>
#include <fstream>
using namespace std;

bool is_sorted_increasing(const vector<int> &vs) {
	for(int i = 0; i < vs.size()-1; ++i) {
		if (!(vs[i] < vs[i+1])) { return false; }
	}
	return true;
}


struct Partition {
	int n;
	vector<int> parts;
	Partition(int n, vector<int> parts) :n(n), parts(parts) {
		assert(is_sorted_increasing(parts));
		int s = 0;
		for(int p : parts) { s += p; }
		assert(s == n);
	};

	Partition(vector<int> parts) : parts(parts) {
		n = 0;
		assert(is_sorted_increasing(parts));
		for(int p : parts) { n += p; }
	}

	void print(std::ostream &s) const {
		s << "[" << n << "|";
		for(int i = 0; i < parts.size(); ++i) {
			s << parts[i];
			if (i < parts.size()-1) { s << " "; }
		}
		s << "]";
	}
};

struct Tableaux {
	vector<vector<int>> xss;
	// entires[r][c]
	Tableaux(vector<vector<int>> xss) : xss(xss) {
	}

	using iterator = vector<vector<int>>::iterator;
	using RowIterator = vector<int>::iterator;

	static bool is_row_increasing(vector<vector<int>> &xss, int r) {
		assert(r < xss.size());
		for(int c = 1; c < xss[r].size(); ++c) {
			if (!(xss[r][c-1] < xss[r][c])) { return false; }
		}
		return true; 
	}

	static bool is_col_increasing(vector<vector<int>> &xss, int c) {
		for(int r = 1; r < xss.size(); ++r) {
			assert(c < xss[r].size());
			if (!(xss[r-1][c] < xss[r][c])) { return false; }
		}
		return true;
	}
};

// RSK algorithm

// insert val at row r.
Tableaux insertAtRow(Tableaux t, int val, int r) {
	assert (r <= t.xss.size());
	if (r == t.xss.size()) {
		t.xss.push_back({val});
		return t;
	}

	Tableaux::RowIterator insertloc = std::upper_bound(t.xss[r].begin(), t.xss[r].end(), val);
	// is larger than all elements. directly insert
	if (insertloc == t.xss[r].end()) {
		t.xss[r].push_back(val);
		return t;
	} else {
		// t is smaller than xss[insertloc]. Kick out insertloc, place t.
		int larger = *insertloc;
		*insertloc = val;
		return insertAtRow(t, larger, r+1); 
	}
}

// insert val into tableaux
Tableaux insert(Tableaux &t, int val) {
	return insertAtRow(t, val, 0);
};


int main() {
	return 0;
}
