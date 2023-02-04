#include <set>
#include <byteswap.h>
#include "solver.h"

#if DEBUG_CHECK_INPUTS
static uint32_t debug_count;
static uint32_t debug_hash;
static uint32_t debug_taken;
#endif

namespace qsym {

namespace {

const uint64_t kUsToS = 1000000;
const int kSessionIdLength = 32;
const unsigned kSolverTimeout = 10000; // 10 seconds

std::string toString6digit(INT32 val) {
  char buf[6 + 1]; // ndigit + 1
  snprintf(buf, 7, "%06d", val);
  buf[6] = '\0';
  return std::string(buf);
}

uint64_t getTimeStamp() {
  struct timeval tv;
  gettimeofday(&tv, NULL);
  return tv.tv_sec * kUsToS + tv.tv_usec;
}

void parseConstSym(ExprRef e, Kind &op, ExprRef& expr_sym, ExprRef& expr_const) {
  for (INT32 i = 0; i < 2; i++) {
    expr_sym = e->getChild(i);
    expr_const = e->getChild(1 - i);
    if (!isConstant(expr_sym)
        && isConstant(expr_const)) {
      op = i == 0 ? e->kind() : swapKind(e->kind());
      return;
    }
  }
  UNREACHABLE();
}

void getCanonicalExpr(ExprRef e,
    ExprRef* canonical,
    llvm::APInt* adjustment=NULL) {
  ExprRef first = NULL;
  ExprRef second = NULL;
  // e == Const + Sym --> canonical == Sym
  switch (e->kind()) {
    // TODO: handle Sub
    case Add:
      first = e->getFirstChild();
      second = e->getSecondChild();
      if (isConstant(first)) {
        *canonical = second;
        if (adjustment != NULL)
          *adjustment =
            static_pointer_cast<ConstantExpr>(first)->value();
        return;
      case Sub:
        // C_0 - Sym
        first = e->getFirstChild();
        second = e->getSecondChild();
        // XXX: need to handle reference count
        if (isConstant(first)) {
          *canonical = g_expr_builder->createNeg(second);
          if (adjustment != NULL)
            *adjustment = static_pointer_cast<ConstantExpr>(first)->value();
          return;
        }
      }
    default:
      break;
  }
  if (adjustment != NULL)
    *adjustment = llvm::APInt(e->bits(), 0);
  *canonical = e;
}

inline bool isEqual(ExprRef e, bool taken) {
  return (e->kind() == Equal && taken) ||
    (e->kind() == Distinct && !taken);
}

} // namespace

Solver::Solver(
    const std::string input_file,
    const std::string out_dir,
    const std::string bitmap)
  : input_file_(input_file)
  , inputs_()
  , out_dir_(out_dir)
  , context_(*g_z3_context)
  , solver_(z3::solver(context_, "QF_BV"))
  , num_generated_(0)
  , trace_(bitmap)
  , last_interested_(false)
  , syncing_(false)
  , start_time_(getTimeStamp())
  , solving_time_(0)
  , last_pc_(0)
  , dep_forest_()
{
  // Set timeout for solver
  z3::params p(context_);
  p.set(":timeout", kSolverTimeout);
  solver_.set(p);

  checkOutDir();
  readInput();
}

void Solver::push() {
  solver_.push();
}

void Solver::reset() {
  solver_.reset();
}

void Solver::pop() {
  solver_.pop();
}

void Solver::add(z3::expr expr) {
  if (!expr.is_const())
    solver_.add(expr.simplify());
}

z3::check_result Solver::check() {
  uint64_t before = getTimeStamp();
  z3::check_result res;
  LOG_STAT(
      "SMT: { \"solving_time\": " + decstr(solving_time_) + ", "
      + "\"total_time\": " + decstr(before - start_time_) + " }\n");
  // LOG_DEBUG("Constraints: " + solver_.to_smt2() + "\n");
  try {
    res = solver_.check();
  }
  catch(z3::exception e) {
    // https://github.com/Z3Prover/z3/issues/419
    // timeout can cause exception
    res = z3::unknown;
  }
  uint64_t cur = getTimeStamp();
  uint64_t elapsed = cur - before;
  solving_time_ += elapsed;
  LOG_STAT("SMT: { \"solving_time\": " + decstr(solving_time_) + " }\n");
  return res;
}

bool Solver::checkAndSave(const std::string& postfix) {
  if (check() == z3::sat) {
    saveValues(postfix);
    return true;
  }
  else {
    LOG_DEBUG("unsat\n");
    return false;
  }
}

void Solver::addJcc(ExprRef e, bool taken, ADDRINT pc) {
  // Save the last instruction pointer for debugging
  last_pc_ = pc;

  if (e->isConcrete())
    return;

  // if e == Bool(true), then ignore
  if (e->kind() == Bool) {
    assert(!(castAs<BoolExpr>(e)->value()  ^ taken));
    return;
  }

  assert(isRelational(e.get()));

  // check duplication before really solving something,
  // some can be handled by range based constraint solving
  bool is_interesting;
  if (pc == 0) {
    // If addJcc() is called by special case, then rely on last_interested_
    is_interesting = last_interested_;
  }
  else
    is_interesting = isInterestingJcc(e, taken, pc);

#if DEBUG_CHECK_INPUTS
  debug_count += 1;
  debug_taken = taken ? 1 : 0;
  debug_hash ^= pc; 

  // printf("DEBUG HASH: %lx - %lx\n", debug_hash, pc);

  static int check_input = -1;
  static uint32_t check_input_count = 0;
  static uint32_t check_input_hash = 0;
  static uint32_t check_input_taken = 0;
  if (check_input == -1) {

    if (getenv("DEBUG_CHECK_INPUT"))
      check_input = 1;
    else
      check_input = 0;

    if (check_input) {
      if (getenv("DEBUG_CHECK_INPUT_COUNT"))
        check_input_count = atoi(getenv("DEBUG_CHECK_INPUT_COUNT"));
      else
        abort();

      if (getenv("DEBUG_CHECK_INPUT_HASH"))
        check_input_hash = strtol(getenv("DEBUG_CHECK_INPUT_HASH"), NULL, 16);
      else
        abort();
      
      if (getenv("DEBUG_CHECK_INPUT_TAKEN"))
        check_input_taken = atoi(getenv("DEBUG_CHECK_INPUT_TAKEN"));
      else
        abort();
    }
  }

  if (check_input) {
    // printf("Checking...\n");
    if (debug_count == check_input_count) {
      if (debug_hash == check_input_hash) {
        if (debug_taken != check_input_taken) {
          printf("Input is taking the expected direction!\n");
          exit(0);
        } else {
          printf("Input is divergent: it reaches the same branch but does not take the expected direction!\n");
          exit(66);
        }
      } else {
        printf("Input is divergent: it does take the same path! [hash is different: %x vs expected=%x]\n", debug_hash, check_input_hash);
        exit(66);
      }
    } else if (debug_count > check_input_count) {
      printf("Input is divergent: it does take the same path! [count is larger]\n");
      exit(66);
    }
  } 
#endif

#if DEBUG_SKIP_QUERIES
  static int skip = -1;
  if (skip == -1) {
    if (getenv("SYMCC_SKIP_QUERIES"))
      skip = 1;
    else
      skip = 0;
  }
  if (skip)
    is_interesting = false;
#endif

  if (is_interesting)
    negatePath(e, taken);
  addConstraint(e, taken, is_interesting);

#if DEBUG_CHECK_PI_SOLVER
  reset();
  printf("Checking PI at %lx\n", pc);
  syncConstraints(e);
  if(solver_.check() == z3::unsat) {
    LOG_FATAL("Adding infeasible constraints: " + std::string(taken ? "" : "!") + e->toString() + "\n");
    abort();
  } else {
    // printf("\nPI OK\n\n");
  }
  reset();
#endif

#if DEBUG_CHECK_PI_CONCRETE
  reset();
  LOG_INFO("Checking PI CONCRETE\n");
  syncConstraints(e);

  z3::expr_vector assertions = solver_.assertions();
  if (assertions.size() > 0) {
    Z3_ast query = z3::mk_and(assertions);
    if(checkConsistencySMT(query, 1) == 0) {
      LOG_FATAL("Adding infeasible constraints: " + std::string(taken ? "" : "!") + e->toString() + "\n");
      abort();
    } else {
      // printf("\nPI OK\n\n");
    }
  }
  reset();
#endif

}

void Solver::addAddr(ExprRef e, ADDRINT addr) {
  llvm::APInt v(e->bits(), addr);
  addAddr(e, v);
}

void Solver::addAddr(ExprRef e, llvm::APInt addr) {
  if (e->isConcrete())
    return;

  if (last_interested_) {
    reset();
    // TODO: add optimize in z3
    syncConstraints(e);
    if (check() != z3::sat)
      return;
    z3::expr &z3_expr = e->toZ3Expr();

    // TODO: add unbound case
    z3::expr min_expr = getMinValue(z3_expr);
    z3::expr max_expr = getMaxValue(z3_expr);
    solveOne(z3_expr == min_expr);
    solveOne(z3_expr == max_expr);
  }

  addValue(e, addr);
}

void Solver::addValue(ExprRef e, ADDRINT val) {
  llvm::APInt v(e->bits(), val);
  addValue(e, v);
}

void Solver::addValue(ExprRef e, llvm::APInt val) {
  if (e->isConcrete())
    return;

#ifdef CONFIG_TRACE
  trace_addValue(e, val);
#endif

  ExprRef expr_val = g_expr_builder->createConstant(val, e->bits());
  ExprRef expr_concrete = g_expr_builder->createBinaryExpr(Equal, e, expr_val);

  addConstraint(expr_concrete, true, false);
}

void Solver::solveAll(ExprRef e, llvm::APInt val) {
  if (last_interested_) {
    std::string postfix = "";
    ExprRef expr_val = g_expr_builder->createConstant(val, e->bits());
    ExprRef expr_concrete = g_expr_builder->createBinaryExpr(Equal, e, expr_val);

    reset();
    syncConstraints(e);
    addToSolver(expr_concrete, false);

    if (check() != z3::sat) {
      // Optimistic solving
      reset();
      addToSolver(expr_concrete, false);
      postfix = "optimistic";
    }

    z3::expr z3_expr = e->toZ3Expr();
    while(true) {
      if (!checkAndSave(postfix))
        break;
      z3::expr value = getPossibleValue(z3_expr);
      add(value != z3_expr);
    }
  }
  addValue(e, val);
}

UINT8 Solver::getInput(ADDRINT index) {
  assert(index < inputs_.size());
  return inputs_[index];
}

void Solver::checkOutDir() {
  // skip if there is no out_dir
  if (out_dir_.empty()) {
    LOG_INFO("Since output directory is not set, use stdout\n");
    return;
  }

  struct stat info;
  if (stat(out_dir_.c_str(), &info) != 0
      || !(info.st_mode & S_IFDIR)) {
    LOG_FATAL("No such directory\n");
    exit(-1);
  }
}

void Solver::readInput() {
  std::ifstream ifs (input_file_, std::ifstream::in | std::ifstream::binary);
  if (ifs.fail()) {
    LOG_FATAL("Cannot open an input file\n");
    exit(-1);
  }

  char ch;
  while (ifs.get(ch))
    inputs_.push_back((UINT8)ch);
}

std::vector<UINT8> Solver::getConcreteValues() {
  // TODO: change from real input
  z3::model m = solver_.get_model();
  unsigned num_constants = m.num_consts();
  std::vector<UINT8> values = inputs_;
  for (unsigned i = 0; i < num_constants; i++) {
    z3::func_decl decl = m.get_const_decl(i);
    z3::expr e = m.get_const_interp(decl);
    z3::symbol name = decl.name();

    if (name.kind() == Z3_INT_SYMBOL) {
      int value = e.get_numeral_int();
      values[name.to_int()] = (UINT8)value;
    }
  }
  return values;
}

void Solver::saveValues(const std::string& postfix) {
  std::vector<UINT8> values = getConcreteValues();

  // If no output directory is specified, then just print it out
  if (out_dir_.empty()) {
    printValues(values);
    return;
  }

  std::string fname = out_dir_+ "/" + toString6digit(num_generated_);
  // Add postfix to record where it is genereated
  if (!postfix.empty())
      fname = fname + "-" + postfix;
#if DEBUG_CHECK_INPUTS
  else {
    static char s_count[16];
    static char s_hash[32];
    sprintf(s_hash, "%x", debug_hash);
    sprintf(s_count, "%d", debug_count);
    fname = fname + "_" + std::string(s_hash) + "_" + std::string(s_count) + "_" + (debug_taken ? "1" : "0");
  }
#endif


  ofstream of(fname, std::ofstream::out | std::ofstream::binary);
  LOG_INFO("New testcase: " + fname + "\n");
  if (of.fail())
    LOG_FATAL("Unable to open a file to write results\n");

      // TODO: batch write
      for (unsigned i = 0; i < values.size(); i++) {
        char val = values[i];
        of.write(&val, sizeof(val));
      }

  of.close();
  num_generated_++;
}

void Solver::printValues(const std::vector<UINT8>& values) {
  fprintf(stderr, "[INFO] Values: ");
  for (unsigned i = 0; i < values.size(); i++) {
    fprintf(stderr, "\\x%02X", values[i]);
  }
  fprintf(stderr, "\n");
}

z3::expr Solver::getPossibleValue(z3::expr& z3_expr) {
  z3::model m = solver_.get_model();
  return m.eval(z3_expr);
}

z3::expr Solver::getMinValue(z3::expr& z3_expr) {
  push();
  z3::expr value(context_);
  while (true) {
    if (checkAndSave()) {
      value = getPossibleValue(z3_expr);
      solver_.add(z3::ult(z3_expr, value));
    }
    else
      break;
  }
  pop();
  return value;
}

z3::expr Solver::getMaxValue(z3::expr& z3_expr) {
  push();
  z3::expr value(context_);
  while (true) {
    if (checkAndSave()) {
      value = getPossibleValue(z3_expr);
      solver_.add(z3::ugt(z3_expr, value));
    }
    else
      break;
  }
  pop();
  return value;
}

void Solver::addToSolver(ExprRef e, bool taken) {
  e->simplify();
  if (!taken)
    e = g_expr_builder->createLNot(e);
  add(e->toZ3Expr());
}

void Solver::syncConstraints(ExprRef e) {
  std::set<std::shared_ptr<DependencyTree<Expr>>> forest;
  DependencySet* deps = e->getDependencies();

  for (const size_t& index : *deps)
    forest.insert(dep_forest_.find(index));

  for (std::shared_ptr<DependencyTree<Expr>> tree : forest) {
    std::vector<std::shared_ptr<Expr>> nodes = tree->getNodes();
    for (std::shared_ptr<Expr> node : nodes) {
      if (isRelational(node.get()))
        addToSolver(node, true);
      else {
        // Process range-based constraints
        bool valid = false;
        for (INT32 i = 0; i < 2; i++) {
          ExprRef expr_range = getRangeConstraint(node, i);
          if (expr_range != NULL) {
            addToSolver(expr_range, true);
            valid = true;
          }
        }

        // One of range expressions should be non-NULL
        if (!valid)
          LOG_INFO(std::string(__func__) + ": Incorrect constraints are inserted\n");
      }
    }
  }

  checkFeasible();
}

void Solver::addConstraint(ExprRef e, bool taken, bool is_interesting) {
  if (auto NE = castAs<LNotExpr>(e)) {
    addConstraint(NE->expr(), !taken, is_interesting);
    return;
  }
  if (!addRangeConstraint(e, taken))
    addNormalConstraint(e, taken);
}

void Solver::addConstraint(ExprRef e) {
  // If e is true, then just skip
  if (e->kind() == Bool) {
    QSYM_ASSERT(castAs<BoolExpr>(e)->value());
    return;
  }
  if (e->isConcrete())
    return;
  dep_forest_.addNode(e);
}

bool Solver::addRangeConstraint(ExprRef e, bool taken) {
  if (!isConstSym(e))
    return false;

  Kind kind = Invalid;
  ExprRef expr_sym, expr_const;
  parseConstSym(e, kind, expr_sym, expr_const);
  ExprRef canonical = NULL;
  llvm::APInt adjustment;
  getCanonicalExpr(expr_sym, &canonical, &adjustment);
  llvm::APInt value = static_pointer_cast<ConstantExpr>(expr_const)->value();

  if (!taken)
    kind = negateKind(kind);

  canonical->addConstraint(kind, value,
      adjustment);
  addConstraint(canonical);
  //updated_exprs_.insert(canonical);
  return true;
}

void Solver::addNormalConstraint(ExprRef e, bool taken) {
  if (!taken)
    e = g_expr_builder->createLNot(e);
  addConstraint(e);
}

ExprRef Solver::getRangeConstraint(ExprRef e, bool is_unsigned) {
  Kind lower_kind = is_unsigned ? Uge : Sge;
  Kind upper_kind = is_unsigned ? Ule : Sle;
  RangeSet *rs = e->getRangeSet(is_unsigned);
  if (rs == NULL)
    return NULL;

  ExprRef expr = NULL;
  for (auto i = rs->begin(), end = rs->end();
      i != end; i++) {
    const llvm::APSInt& from = i->From();
    const llvm::APSInt& to = i->To();
    ExprRef bound = NULL;

    if (from == to) {
      // can simplify this case
      ExprRef imm = g_expr_builder->createConstant(from, e->bits());
      bound = g_expr_builder->createEqual(e, imm);
    }
    else
    {
      ExprRef lb_imm = g_expr_builder->createConstant(i->From(), e->bits());
      ExprRef ub_imm = g_expr_builder->createConstant(i->To(), e->bits());
      ExprRef lb = g_expr_builder->createBinaryExpr(lower_kind, e, lb_imm);
      ExprRef ub = g_expr_builder->createBinaryExpr(upper_kind, e, ub_imm);
      bound = g_expr_builder->createLAnd(lb, ub);
    }

    if (expr == NULL)
      expr = bound;
    else
      expr = g_expr_builder->createLOr(expr, bound);
  }

  return expr;
}


bool Solver::isInterestingJcc(ExprRef rel_expr, bool taken, ADDRINT pc) {
  bool interesting = trace_.isInterestingBranch(pc, taken);
  // record for other decision
  last_interested_ = interesting;
  return interesting;
}

void Solver::negatePath(ExprRef e, bool taken) {
  reset();
  syncConstraints(e);
  addToSolver(e, !taken);
  // printf("CONSTRAINT: %s\n", e->toString().c_str());
  bool sat = checkAndSave();
  if (!sat) {
    reset();
    // optimistic solving
    addToSolver(e, !taken);
    checkAndSave("optimistic");
  }
}

void Solver::solveOne(z3::expr z3_expr) {
  push();
  add(z3_expr);
  checkAndSave();
  pop();
}

void Solver::checkFeasible() {
#ifdef CONFIG_TRACE
  if (check() == z3::unsat)
    LOG_FATAL("Infeasible constraints: " + solver_.to_smt2() + "\n");
#endif
}

#if DEBUG_CONSISTENCY_CHECK || DEBUG_CHECK_PI_CONCRETE

uint64_t Solver::concreteEvalute(Z3_ast e) {
  static Z3_model m = NULL;
  if (m == NULL) {
    Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
    std::vector<UINT8> values = inputs_;
    m = Z3_mk_model(context_);
    Z3_model_inc_ref(context_, m);
    Z3_sort sort = Z3_mk_bv_sort(context_, 8);
    for (size_t i = 0; i < inputs_.size(); i++) {

      z3::symbol s = context_.int_symbol(i);
      z3::expr v = context_.bv_val(inputs_[i], 8);
      
      // printf("%s\n", Z3_ast_to_string(context_, v));

      Z3_func_decl decl = Z3_mk_func_decl(context_, s, 0, NULL, sort);
      Z3_add_const_interp(context_, m, decl, v);
    }

    // printf("Model:\n%s\n", Z3_model_to_string(context_, m));
  }

  // printf("EXPR: %s\n", Z3_ast_to_string(context_, e));

  uint64_t  value;
  Z3_ast    solution;
  Z3_bool   successfulEval =
      Z3_model_eval(context_, m, e, Z3_TRUE, &solution);
  assert(successfulEval && "Failed to evaluate model");

  if (Z3_get_ast_kind(context_, solution) == Z3_NUMERAL_AST) {

    Z3_bool successGet =
          Z3_get_numeral_uint64(context_, solution, (uint64_t*)&value);
    assert(successGet);
    return value;

  } else {

    Z3_lbool res = Z3_get_bool_value(context_, solution);
    if (res == Z3_L_TRUE) return 1;
    else if (res == Z3_L_FALSE) return 0;
    else {
      printf("KIND: %x\n", Z3_get_ast_kind(context_, solution));
      Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
      printf("EXPR: %s\n", Z3_ast_to_string(context_, e));
      assert(0 && "Cannot evaluate");
      abort();
    }
  }
}

int Solver::checkConsistencySMT(Z3_ast e, uint64_t expected_value) {

  uint64_t value = concreteEvalute(e);

  if (Z3_get_ast_kind(context_, e) == Z3_NUMERAL_AST) {
    if (value != expected_value) {
      Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
      printf("%s\n", Z3_ast_to_string(context_, e));
      printf("FAILURE: %lx vs expected=%lx\n", value, expected_value);
    } else {
      printf("SUCCESS: %lx vs expected=%lx\n", value, expected_value);
    }
    return value == expected_value;
  } else {
    if (value != expected_value) {
      Z3_set_ast_print_mode(context_, Z3_PRINT_LOW_LEVEL);
      // printf("%s\n", Z3_ast_to_string(context_, e));
      printf("BOOL FAILURE: %lx vs expected=%lx\n", value, expected_value);
    }
    return value == expected_value;
  }  
}

static uint64_t fuzz_check_count = 0;
void Solver::saveDebugValues(uint64_t value, int n) {
  std::vector<UINT8> values = getConcreteValues();

  // If no output directory is specified, then just print it out
  if (out_dir_.empty()) {
    printValues(values);
    return;
  }

  static char s_value[32];
  sprintf(s_value, "%lx", value);
  std::string fname = out_dir_+ "/debug_" + toString6digit(fuzz_check_count) + "_" + std::string(s_value) + "_" + std::to_string(n);

  ofstream of(fname, std::ofstream::out | std::ofstream::binary);
  LOG_INFO("DEBUG testcase: " + fname + "\n");
  if (of.fail())
    LOG_FATAL("Unable to open a file to write results\n");

      // TODO: batch write
      for (unsigned i = 0; i < values.size(); i++) {
        char val = values[i];
        of.write(&val, sizeof(val));
      }

  of.close();
}

int Solver::checkConsistency(ExprRef e, uint64_t expected_value) {
  int res = checkConsistencySMT(e->toZ3Expr(), expected_value);

#if DEBUG_FUZZ_EXPRS

  int fuzz_expr = -1;
  uint64_t fuzz_count = 0;
  uint64_t fuzz_value = 0;
  if (fuzz_expr == -1) {

    if (getenv("DEBUG_FUZZ_EXPR"))
      fuzz_expr = 1;
    else
      fuzz_expr = 0;

    if (fuzz_expr) {
      if (getenv("DEBUG_FUZZ_EXPR_COUNT"))
        fuzz_count = atoi(getenv("DEBUG_FUZZ_EXPR_COUNT"));
      else
        abort();

      if (getenv("DEBUG_FUZZ_EXPR_VALUE"))
        fuzz_value = strtol(getenv("DEBUG_FUZZ_EXPR_VALUE"), NULL, 16);
      else
        abort();
    }
  }

  fuzz_check_count += 1;
  if (fuzz_expr) {
    if (fuzz_count == fuzz_check_count) {
      if (fuzz_value == expected_value) {
        printf("Expression has expected value!\n");
        exit(0);
      } else {
        printf("Expression has wrong value [%lx vs expected=%lx]\n", expected_value, fuzz_value);
        exit(66);
      }
    } else if (fuzz_count < fuzz_check_count) {
      printf("Expression check has been bypassed [count is larger]\n");
      exit(66);
    }
    return res;
  }

  reset();
  syncConstraints(e);
  z3::expr expr = e->toZ3Expr();
  solver_.push();
  uint64_t current_value = expected_value;
  for (int i = 0; i < DEBUG_FUZZ_EXPRS_N; i++) {
    bool is_bool = isRelational(e.get());
    z3::expr not_e = is_bool 
      ? g_expr_builder->createLNot(e)->toZ3Expr() 
      : g_expr_builder->createDistinct(e, g_expr_builder->createConstant(current_value, e->bits()))->toZ3Expr();
    solver_.add(not_e);
    z3::check_result feasible = solver_.check();
    if (feasible == z3::sat) {
      Z3_model model = solver_.get_model();
      Z3_ast solution = nullptr;
      Z3_model_eval(context_, model, expr, Z3_TRUE, &solution);
      uint64_t value = 0;
      if (is_bool) {
        Z3_lbool res = Z3_get_bool_value(context_, solution);
        if (res == Z3_L_TRUE)
          value = 1;
        else if (res == Z3_L_FALSE)
          value = 0;
        else
          abort();
      } else
        Z3_get_numeral_uint64(context_, solution, &value);
      assert(current_value != value);
      current_value = value;
      saveDebugValues(value, i);
    } 
    if (is_bool) break;
  }
  solver_.pop();
  reset();
#endif

  return res;
}

void Solver::checkConsistencyOpt(ExprRef e0, ExprRef e1) {
  printf("CHECKING OPT\n");
  uint64_t v0 = concreteEvalute(e0->toZ3Expr());
  uint64_t v1 = concreteEvalute(e1->toZ3Expr());
  if (v0 != v1) {
    printf("[EVAL] Invalid expression optimization!\n");
    printf("E0: %s\n", e0->toString().c_str());
    printf("E1: %s\n", e1->toString().c_str()); 
    abort();
  }

  reset();
  ExprRef c = g_expr_builder->createDistinct(e0, e1);
  addToSolver(c, true);
  if (c->kind() != Bool && check() == z3::sat) {
    printf("[SAT] Invalid expression optimization!\n");
    printf("E0: %s\n", e0->toString().c_str());
    printf("E1: %s\n", e1->toString().c_str()); 
    printf("CHECK: %s\n", c->toString().c_str());
    checkAndSave("correctness");
    // const char* s = Z3_solver_to_string(context_, solver_);
    // printf("SOLVER:\n%s\n", s ? s : "NULL");
    abort();
  }
  reset();
}
#endif

} // namespace qsym
