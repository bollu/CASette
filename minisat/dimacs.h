// Authors: Siddharth Bhat
// parser for SMT-LIB-2 expressions.
// https://jix.github.io/varisat/manual/0.2.0/formats/dimacs.html
#pragma once
#include "minisat.h"
#include <optional>
#include <sstream>
#include <iostream>

// From the drat-trim page.
// <formula>   = { <comment> } "p cnf " <var-max> " " <num-cls> "\n" <cnf>
// <cnf>       = { <comment> | <clause> }
// <comment>   = "c " <anything> "\n"
// <clause>    = { <blank> }{ <lit> } "0"
// <lit>       = <pos> <blank> | <neg> <blank>
// <pos>       = "1" | "2" | .... | <max-idx>
// <neg>       = "-" <pos>
// <blank>     = " " | "\n" | "\t"


namespace dimacs {
  using namespace std;

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-function"

  // returns 'false' if conflict was found when parsing header.
  static bool parse_header(std::istream &f, Solver *S) {
    std::string line;
    while (std::getline(f, line)) {
      if (line.empty()) continue; // Skip empty lines
      std::istringstream iss(line);
      char firstChar = line[0];
      int nof_vars = -1;
      int nof_clauses = -1;
      if (firstChar == 'c') {
        // Skip comments
        continue;
      } else if (firstChar == 'p') {
        // Parse the problem line
        std::string format;
        iss >> firstChar >> format >> nof_vars >> nof_clauses;
        assert(format == "cnf" && "format expected to be CNF");
        assert(nof_vars > -1 && "expected to see 'p' line with number of variables");
        for(int i = 0; i < nof_vars; ++i) {
          S->newVar(); // make a variable for each 'var'.
        }
      } else {
        assert(nof_vars > -1 && "expected to see 'p' line with number of variables");
        assert (nof_clauses > -1);
        // Parse a clause
        std::vector<lit> clause;
        int raw_lit = -1;
        while (iss >> raw_lit && raw_lit != 0) {
          const bool pos = raw_lit > 0;
          const var v = pos ? raw_lit : -raw_lit;
          const lit l = lit(v, pos);
          clause.push_back(l);
        }
        if (!S->addClause(clause)) {
          return false;
        }
      } // end else(), parsing everything else.
    } // end while
    return true;
  } // end parse_header
#pragma clang diagnostic pop
}

