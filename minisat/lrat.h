// Authors: Siddharth Bhat
// LRAT Proof emitter.
// Adapted from cadical's proof tracer.
// https://github.com/arminbiere/cadical/blob/31f9aae44947c673dc6190c9beb399acb9ffec6a/src/tracer.hpp



struct LRATEmitter {

  enum class ConclusionType { CONFLICT = 1, ASSUMPTIONS = 2, CONSTRAINT = 4 };
  using clauseId = uint64_t;

  virtual ~LRATEmitter() = 0;
  // Notify the tracer that a original clause has been added.
  //
  virtual void add_original_clause (clauseId id, const std::vector<lit> &clause);

  // Notify the observer that a new clause has been derived.
  // Includes ID and wether the clause is redundant or irredundant
  // If antecedents are derived they will be included here.
  // Arguments: ID, redundant, clause, antecedents
  //
  virtual void add_derived_clause (clauseId id, const std::vector<lit> & clause, const std::vector<clauseId> &antecedents) {}

  // Notify the observer that a clause is deleted.
  // Includes ID and redundant/irredundant
  // Arguments: ID, redundant, clause
  //
  virtual void delete_clause (clauseId id, const std::vector<lit> &clause) {}


  // Notify the observer that the solve call ends with status StatusType
  // If the status is UNSAT and an empty clause has been derived, the second
  // argument will contain its id.
  // Note that the empty clause is already added through add_derived_clause
  // and finalized with finalize_clause
  virtual void report_status (int status, clauseId unsat_clause) {}

  /*------------------------------------------------------------------------*/
  /*                                                                        */
  /*                   Specifically non-incremental */
  /*                                                                        */
  /*------------------------------------------------------------------------*/

  // Notify the observer that a clause is finalized.
  // Arguments: ID, clause
  //
  virtual void finalize_clause (clauseId id, const std::vector<lit> &clause) {}

  // Notify the observer that the proof begins with a set of reserved ids
  // for original clauses. Given ID is the first derived clause ID.
  // Arguments: ID
  //
  virtual void begin_proof (clauseId reserved_ids) {}

  // /*------------------------------------------------------------------------*/
  // /*                                                                        */
  // /*                      Specifically incremental */
  // /*                                                                        */
  // /*------------------------------------------------------------------------*/

  // // Notify the observer that an assumption has been added
  // // Arguments: assumption_literal
  // //
  // virtual void solve_query () {}

  // // Notify the observer that an assumption has been added
  // // Arguments: assumption_literal
  // //
  // virtual void add_assumption (int) {}

  // // Notify the observer that a constraint has been added
  // // Arguments: constraint_clause
  // //
  // virtual void add_constraint (const std::vector<int> &) {}

  // // Notify the observer that assumptions and constraints are reset
  // //
  // virtual void reset_assumptions () {}

  // // Notify the observer that this clause could be derived, which
  // // is the negation of a core of failing assumptions/constraints.
  // // If antecedents are derived they will be included here.
  // // Arguments: ID, clause, antecedents
  // //
  // virtual void add_assumption_clause (uint64_t, const std::vector<int> &,
  //                                     const std::vector<uint64_t> &) {}

  // // Notify the observer that conclude unsat was requested.
  // // will give either the id of the empty clause, the id of a failing
  // // assumption clause or the ids of the failing constrain clauses
  // // Arguments: conclusion_type, clause_ids
  // //
  // virtual void conclude_unsat (ConclusionType,
  //                              const std::vector<uint64_t> &) {}

  // // Notify the observer that conclude sat was requested.
  // // will give the complete model as a vector.
  // virtual void conclude_sat (const std::vector<int> &) {}
};
