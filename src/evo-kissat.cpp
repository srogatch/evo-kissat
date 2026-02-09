#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cctype>
#include <cinttypes>
#include <cmath>
#include <cstring>
#include <limits>
#include <mutex>
#include <random>
#include <string>
#include <thread>
#include <unordered_set>
#include <vector>
#include <unistd.h>

extern "C" {
#include "config.h"
#include "file.h"
#include "kissat.h"
#include "literal.h"
#include "options.h"
#include "resources.h"
// local witness printing (avoid linking application objects)
}

struct Formula {
  std::vector<int> lits;
  int max_var = 0;
  uint64_t clauses = 0;
};

struct SharedClause {
  unsigned glue = 0;
  std::vector<int> lits;
};

static void print_witness (kissat *solver, int max_var, bool partial) {
  std::vector<char> buffer;
  buffer.reserve (128);
  auto flush = [&]() {
    fputs ("v", stdout);
    for (char ch : buffer)
      fputc (ch, stdout);
    fputc ('\n', stdout);
    buffer.clear ();
  };
  auto print_int = [&](int i) {
    char tmp[16];
    sprintf (tmp, " %d", i);
    size_t tmp_len = strlen (tmp);
    if (buffer.size () + tmp_len > 77)
      flush ();
    buffer.insert (buffer.end (), tmp, tmp + tmp_len);
  };
  for (int eidx = 1; eidx <= max_var; eidx++) {
    int tmp = kissat_value (solver, eidx);
    if (!tmp && !partial)
      tmp = eidx;
    if (tmp)
      print_int (tmp);
  }
  print_int (0);
  if (!buffer.empty ())
    flush ();
}

struct SharedPool {
  std::mutex mutex;
  std::unordered_set<int> units;
  std::unordered_set<uint64_t> binaries;
  std::vector<SharedClause> clauses;
  size_t max_clauses = 0;
};

static uint64_t encode_binary_key (int a, int b) {
  if (b < a)
    std::swap (a, b);
  const uint32_t lo = (uint32_t) (int32_t) a;
  const uint32_t hi = (uint32_t) (int32_t) b;
  return ((uint64_t) lo << 32) | hi;
}

static std::array<int, 2> decode_binary_key (uint64_t key) {
  const uint32_t lo = (uint32_t) (key >> 32);
  const uint32_t hi = (uint32_t) key;
  return {(int) (int32_t) lo, (int) (int32_t) hi};
}

struct ActiveSolvers {
  std::mutex mutex;
  std::vector<kissat *> solvers;
};

static void register_solver (ActiveSolvers &active, kissat *solver) {
  std::lock_guard<std::mutex> lock (active.mutex);
  active.solvers.push_back (solver);
}

static void unregister_solver (ActiveSolvers &active, kissat *solver) {
  std::lock_guard<std::mutex> lock (active.mutex);
  for (size_t i = 0; i < active.solvers.size (); i++) {
    if (active.solvers[i] == solver) {
      active.solvers[i] = active.solvers.back ();
      active.solvers.pop_back ();
      break;
    }
  }
}

static void terminate_active (ActiveSolvers &active) {
  std::lock_guard<std::mutex> lock (active.mutex);
  for (kissat *solver : active.solvers)
    kissat_terminate (solver);
}

struct EvoOptions {
  bool quiet = false;
  bool witness = true;
  bool statistics = false;
  bool partial = false;
  int verbose = 0;
  int conflicts_limit = 10000;
  int decisions_limit = -1;
  int time_limit = 0;
  int eval_time_limit = 10;
  std::string input_path;
  std::string config;
  std::vector<std::pair<std::string, int>> overrides;

  unsigned threads = 0;
  unsigned population = 0;
  unsigned max_evals = 0;
  unsigned share_in = 200;
  unsigned share_out = 200;
  unsigned share_pool = 50000000;
  unsigned share_max_size = 12;
  unsigned share_max_glue = 4;
  unsigned evo_seed = 0;
};

struct GeneSpec {
  const opt *option = nullptr;
  int low = 0;
  int high = 0;
  bool is_bool = false;
};

struct Genome {
  std::vector<int> values;
  std::vector<int8_t> phases;
  unsigned seed = 0;
};

struct Result {
  Genome genome;
  double unfitness = 0.0;
  int status = 0;
  double elapsed = 0.0;
  bool improved = false;
  bool evaluated = false;
  bool aborted = false;
  unsigned remaining_vars = 0;
  uint64_t remaining_clauses = 0;
  uint64_t remaining_binary = 0;
};

struct TerminationState {
  std::atomic<bool> *stop = nullptr;
  std::atomic<bool> *abort = nullptr;
  double deadline = 0.0;
};

static int terminate_cb (void *ptr) {
  const TerminationState *state = static_cast<TerminationState *> (ptr);
  if (state->stop && state->stop->load ())
    return 1;
  if (state->abort && state->abort->load ())
    return 1;
  if (state->deadline > 0 && kissat_wall_clock_time () >= state->deadline)
    return 1;
  return 0;
}

static unsigned pick_threads () {
  unsigned res = std::thread::hardware_concurrency ();
  if (res)
    return res;
#ifdef _POSIX_C_SOURCE
  long tmp = sysconf (_SC_NPROCESSORS_ONLN);
  if (tmp > 0)
    return (unsigned) tmp;
#endif
  return 4;
}

static void print_usage (const char *name) {
  printf ("usage: %s [<option> ... ] [ <dimacs> ]\n", name);
  printf ("\n");
  printf ("Evolutionary parallel solver based on Kissat.\n");
  printf ("Common options (subset of kissat):\n");
  printf ("  -h, --help                 print this help\n");
  printf ("  -n                         do not print satisfying assignment\n");
  printf ("  -q                         suppress all messages\n");
  printf ("  -s                         print complete statistics\n");
  printf ("  -v                         increase verbosity\n");
  printf ("  --partial                  print partial witness\n");
  printf ("  --conflicts=<limit>        per-evaluation conflict limit\n");
  printf ("  --decisions=<limit>        per-evaluation decision limit\n");
  printf ("  --time=<seconds>           global time limit\n");
  printf ("  --<option>=<value>         set Kissat option\n");
  printf ("  --basic/--plain/--sat/--unsat/--default\n");
  printf ("\n");
  printf ("Evolution options:\n");
  printf ("  --evo-pop=<n>              population size\n");
  printf ("  --evo-evals=<n>            max evaluations (0 = unlimited)\n");
  printf ("  --evo-conflicts=<n>        alias for --conflicts\n");
  printf ("  --evo-share=<n>            large clauses imported per evaluation\n");
  printf ("  --evo-share-out=<n>        large clauses exported per evaluation\n");
  printf ("  --evo-share-pool=<n>       shared pool size\n");
  printf ("  --evo-share-size=<n>       max shared clause size\n");
  printf ("  --evo-share-glue=<n>       max shared clause glue\n");
  printf ("  --evo-eval-time=<n>        per-evaluation time budget (seconds, 0 = no limit)\n");
  printf ("  --evo-threads=<n>          worker threads\n");
  printf ("  --evo-seed=<n>             RNG seed\n");
}

static bool parse_int_option (const char *arg, const char *name, int &out) {
  const char *val = kissat_parse_option_name (arg, name);
  if (!val)
    return false;
  int tmp = 0;
  if (!kissat_parse_option_value (val, &tmp))
    return false;
  out = tmp;
  return true;
}

static bool parse_uint_option (const char *arg, const char *name,
                               unsigned &out) {
  int tmp = 0;
  if (!parse_int_option (arg, name, tmp))
    return false;
  if (tmp < 0)
    return false;
  out = (unsigned) tmp;
  return true;
}

static bool parse_args (int argc, char **argv, EvoOptions &opts) {
  for (int i = 1; i < argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h") || !strcmp (arg, "--help")) {
      print_usage (argv[0]);
      return false;
    } else if (!strcmp (arg, "-n"))
      opts.witness = false;
    else if (!strcmp (arg, "-q"))
      opts.quiet = true;
    else if (!strcmp (arg, "-s"))
      opts.statistics = true;
    else if (!strcmp (arg, "-v"))
      opts.verbose++;
    else if (!strcmp (arg, "--partial"))
      opts.partial = true;
    else if (parse_int_option (arg, "conflicts", opts.conflicts_limit))
      ;
    else if (parse_int_option (arg, "decisions", opts.decisions_limit))
      ;
    else if (parse_int_option (arg, "time", opts.time_limit))
      ;
    else {
      unsigned tmp = 0;
      if (parse_uint_option (arg, "evo-conflicts", tmp))
        opts.conflicts_limit = (int) tmp;
      else if (parse_uint_option (arg, "evo-pop", opts.population))
        ;
      else if (parse_uint_option (arg, "evo-evals", opts.max_evals))
        ;
      else if (parse_uint_option (arg, "evo-share", opts.share_in))
        ;
      else if (parse_uint_option (arg, "evo-share-out", opts.share_out))
        ;
      else if (parse_uint_option (arg, "evo-share-pool", opts.share_pool))
        ;
      else if (parse_uint_option (arg, "evo-share-size", opts.share_max_size))
        ;
      else if (parse_uint_option (arg, "evo-share-glue", opts.share_max_glue))
        ;
      else if (parse_int_option (arg, "evo-eval-time", opts.eval_time_limit))
        ;
      else if (parse_uint_option (arg, "evo-threads", opts.threads))
        ;
      else if (parse_uint_option (arg, "evo-seed", opts.evo_seed))
        ;
      else if (!strncmp (arg, "--", 2) &&
               kissat_has_configuration (arg + 2)) {
        opts.config = arg + 2;
      } else if (!strncmp (arg, "--", 2)) {
#ifndef NOPTIONS
        char name[kissat_options_max_name_buffer_size];
        int value = 0;
        if (!kissat_options_parse_arg (arg, name, &value)) {
          fprintf (stderr, "invalid option '%s'\n", arg);
          return false;
        }
        opts.overrides.emplace_back (name, value);
#else
        fprintf (stderr, "options disabled, unknown option '%s'\n", arg);
        return false;
#endif
      } else if (arg[0] == '-') {
        fprintf (stderr, "unknown option '%s'\n", arg);
        return false;
      } else if (opts.input_path.empty ()) {
        opts.input_path = arg;
      } else {
        fprintf (
            stderr,
            "unexpected argument '%s' (proof output not supported)\n",
            arg);
        return false;
      }
    }
    continue;
  }
  if (opts.eval_time_limit < 0) {
    fprintf (stderr, "invalid --evo-eval-time=%d\n", opts.eval_time_limit);
    return false;
  }
  return true;
}

struct Scanner {
  file *file_handle;
  int pending = EOF;
  uint64_t line = 1;
  bool at_line_start = true;

  int get () {
    if (pending != EOF) {
      const int ch = pending;
      pending = EOF;
      return ch;
    }
    return kissat_getc (file_handle);
  }

  void putback (int ch) { pending = ch; }
};

static bool parse_dimacs (const char *path, Formula &formula) {
  file file;
  if (!path || !*path || !strcmp (path, "-"))
    kissat_read_already_open_file (&file, stdin, "<stdin>");
  else if (!kissat_open_to_read_file (&file, path))
    return false;

  Scanner scanner;
  scanner.file_handle = &file;

  std::vector<int> clause;

  for (;;) {
    int ch = scanner.get ();
    if (ch == EOF)
      break;
    if (ch == '\r')
      continue;
    if (ch == '\n') {
      scanner.at_line_start = true;
      scanner.line++;
      continue;
    }
    if (std::isspace ((unsigned char) ch))
      continue;

    if (scanner.at_line_start && ch == 'c') {
      while ((ch = scanner.get ()) != EOF && ch != '\n')
        ;
      if (ch == '\n') {
        scanner.at_line_start = true;
        scanner.line++;
      }
      continue;
    }

    if (scanner.at_line_start && ch == 'p') {
      while ((ch = scanner.get ()) != EOF && ch != '\n')
        ;
      if (ch == '\n') {
        scanner.at_line_start = true;
        scanner.line++;
      }
      continue;
    }

    scanner.at_line_start = false;

    int sign = 1;
    if (ch == '-') {
      sign = -1;
      ch = scanner.get ();
      if (!std::isdigit ((unsigned char) ch)) {
        fprintf (stderr, "parse error at line %" PRIu64 "\n",
                 scanner.line);
        kissat_close_file (&file);
        return false;
      }
    }
    if (!std::isdigit ((unsigned char) ch)) {
      fprintf (stderr, "parse error at line %" PRIu64 "\n", scanner.line);
      kissat_close_file (&file);
      return false;
    }
    int idx = ch - '0';
    while (std::isdigit ((unsigned char) (ch = scanner.get ()))) {
      // Keep parsing bounded to the same external literal range that
      // `kissat_add` accepts, instead of letting malformed numbers reach it.
      if (EXTERNAL_MAX_VAR / 10 < idx) {
        fprintf (stderr, "parse error at line %" PRIu64 "\n", scanner.line);
        kissat_close_file (&file);
        return false;
      }
      idx *= 10;
      const int digit = ch - '0';
      if (EXTERNAL_MAX_VAR - digit < idx) {
        fprintf (stderr, "parse error at line %" PRIu64 "\n", scanner.line);
        kissat_close_file (&file);
        return false;
      }
      idx += digit;
    }
    if (ch != EOF)
      scanner.putback (ch);
    const int val = sign * idx;

    if (!val) {
      formula.clauses++;
      formula.lits.insert (formula.lits.end (), clause.begin (),
                           clause.end ());
      formula.lits.push_back (0);
      clause.clear ();
      continue;
    }

    if (idx > formula.max_var)
      formula.max_var = idx;
    clause.push_back (val);
  }

  if (!clause.empty ()) {
    fprintf (stderr, "parse error: incomplete clause at end of file\n");
    kissat_close_file (&file);
    return false;
  }

  kissat_close_file (&file);
  return true;
}

static std::vector<GeneSpec> build_gene_specs () {
  std::vector<GeneSpec> specs;
#ifndef NOPTIONS
  const char *names[] = {"restart",  "restartint", "reduce",    "reduceint",
                         "rephase",  "rephaseint", "reorder",   "reorderint",
                         "stable",   "target",     "randec",    "randecinit",
                         "randecint","randecstable","walkinitially",
                         "walkeffort","phase",     "forcephase","phasesaving",
                         "tumble",   "sweep",      "probe",     "eliminate",
                         "vivify",   "preprocess", "minimize",  "chrono"};
  for (const char *name : names) {
    const opt *o = kissat_options_has (name);
    if (!o)
      continue;
    GeneSpec spec;
    spec.option = o;
    spec.low = o->low;
    spec.high = o->high;
    spec.is_bool = (o->low == 0 && o->high == 1);
    specs.push_back (spec);
  }
#else
#endif
  return specs;
}

static std::vector<int> build_base_values (
    const std::vector<GeneSpec> &specs,
    const std::vector<std::pair<std::string, int>> &overrides) {
  std::vector<int> values;
  values.reserve (specs.size ());
  for (const auto &spec : specs) {
    int value = spec.option->value;
    for (const auto &ov : overrides)
      if (ov.first == spec.option->name)
        value = ov.second;
    values.push_back (value);
  }
  return values;
}

static int clamp_int (int v, int lo, int hi) {
  if (v < lo)
    return lo;
  if (v > hi)
    return hi;
  return v;
}

static int mutate_value (const GeneSpec &spec, int base,
                         std::mt19937 &rng) {
  if (spec.is_bool)
    return base ? 0 : 1;
  std::uniform_int_distribution<int> dist (spec.low, spec.high);
  const int span = spec.high - spec.low;
  if (span <= 16)
    return dist (rng);
  std::normal_distribution<double> n (0.0, span / 10.0);
  int mutated = base + (int) std::llround (n (rng));
  return clamp_int (mutated, spec.low, spec.high);
}

static Genome random_genome (const std::vector<GeneSpec> &specs,
                             const std::vector<int> &base, unsigned vars,
                             std::mt19937 &rng) {
  Genome g;
  g.values = base;
  std::uniform_real_distribution<double> p (0.0, 1.0);
  for (size_t i = 0; i < specs.size (); i++)
    if (p (rng) < 0.35)
      g.values[i] = mutate_value (specs[i], g.values[i], rng);
  g.phases.resize (vars);
  std::bernoulli_distribution b (0.5);
  for (unsigned i = 0; i < vars; i++)
    g.phases[i] = b (rng) ? 1 : -1;
  g.seed = rng ();
  return g;
}

static Genome crossover (const Genome &a, const Genome &b,
                         const std::vector<GeneSpec> &specs,
                         std::mt19937 &rng) {
  Genome g;
  g.values.resize (specs.size ());
  std::uniform_int_distribution<int> pick (0, 1);
  for (size_t i = 0; i < specs.size (); i++)
    g.values[i] = pick (rng) ? a.values[i] : b.values[i];
  g.seed = pick (rng) ? a.seed : b.seed;
  const size_t vars = a.phases.size ();
  g.phases.resize (vars);
  if (vars) {
    std::uniform_int_distribution<size_t> split (0, vars);
    const size_t cut = split (rng);
    for (size_t i = 0; i < cut; i++)
      g.phases[i] = a.phases[i];
    for (size_t i = cut; i < vars; i++)
      g.phases[i] = b.phases[i];
  }
  return g;
}

static void mutate_genome (Genome &g, const std::vector<GeneSpec> &specs,
                           std::mt19937 &rng) {
  std::uniform_real_distribution<double> p (0.0, 1.0);
  for (size_t i = 0; i < specs.size (); i++)
    if (p (rng) < 0.15)
      g.values[i] = mutate_value (specs[i], g.values[i], rng);
  if (!g.phases.empty ()) {
    const double phase_mutation_rate = 0.01;
    for (size_t i = 0; i < g.phases.size (); i++) {
      if (p (rng) < phase_mutation_rate) {
        int8_t v = g.phases[i];
        if (!v)
          v = p (rng) < 0.5 ? 1 : -1;
        else
          v = -v;
        g.phases[i] = v;
      }
    }
  }
  if (p (rng) < 0.5)
    g.seed = rng ();
}

static void apply_options (kissat *solver, const EvoOptions &opts,
                           const Genome &g,
                           const std::vector<GeneSpec> &specs) {
  if (!opts.config.empty ())
    kissat_set_configuration (solver, opts.config.c_str ());
  for (const auto &ov : opts.overrides)
    kissat_set_option (solver, ov.first.c_str (), ov.second);
  for (size_t i = 0; i < specs.size (); i++)
    kissat_set_option (solver, specs[i].option->name, g.values[i]);
  kissat_set_option (solver, "seed", (int) g.seed);
  kissat_set_option (solver, "quiet", 1);
  if (opts.statistics)
    kissat_set_option (solver, "statistics", 1);
  if (opts.verbose > 0)
    kissat_set_option (solver, "verbose", opts.verbose);
}

static void import_shared (kissat *solver, const Formula &formula,
                           SharedPool &pool, unsigned limit,
                           std::mt19937 &rng) {
  std::vector<int> units;
  std::vector<std::array<int, 2>> binaries;
  std::vector<SharedClause> subset;
  {
    std::lock_guard<std::mutex> lock (pool.mutex);
    units.reserve (pool.units.size ());
    for (int lit : pool.units)
      units.push_back (lit);
    binaries.reserve (pool.binaries.size ());
    for (uint64_t key : pool.binaries)
      binaries.push_back (decode_binary_key (key));
    if (limit && !pool.clauses.empty ()) {
      const size_t n = std::min<size_t> (limit, pool.clauses.size ());
      subset.reserve (n);
      std::uniform_int_distribution<size_t> dist (0,
                                                  pool.clauses.size () - 1);
      for (size_t i = 0; i < n; i++) {
        const size_t idx = dist (rng);
        subset.push_back (pool.clauses[idx]);
      }
    }
  }
  // Import all pooled units/binaries into every evaluation. These are the
  // strongest constraints and should be shared globally across generations.
  for (int lit : units) {
    if (std::abs (lit) > formula.max_var)
      continue;
    if (kissat_import_shared_clause (solver, 1, &lit, 1) == 2)
      return;
  }
  for (const auto &binary : binaries) {
    if (std::abs (binary[0]) > formula.max_var ||
        std::abs (binary[1]) > formula.max_var)
      continue;
    const int pair[2] = {binary[0], binary[1]};
    if (kissat_import_shared_clause (solver, 2, pair, 1) == 2)
      return;
  }
  for (const auto &cl : subset)
    if (kissat_import_shared_clause (solver, (unsigned) cl.lits.size (),
                                     cl.lits.data (), cl.glue) == 2)
      return;
}

struct ExportContext {
  SharedPool *pool;
  size_t max_pool;
  std::mt19937 *rng;
};

static int export_shared_clause (void *state, unsigned size, unsigned glue,
                                 const int *lits) {
  ExportContext *ctx = static_cast<ExportContext *> (state);
  if (size == 1) {
    std::lock_guard<std::mutex> lock (ctx->pool->mutex);
    ctx->pool->units.insert (lits[0]);
    return 0;
  }
  if (size == 2) {
    std::lock_guard<std::mutex> lock (ctx->pool->mutex);
    ctx->pool->binaries.insert (encode_binary_key (lits[0], lits[1]));
    return 0;
  }
  SharedClause cl;
  cl.glue = glue;
  cl.lits.assign (lits, lits + size);
  std::lock_guard<std::mutex> lock (ctx->pool->mutex);
  if (ctx->pool->clauses.size () < ctx->max_pool) {
    ctx->pool->clauses.push_back (std::move (cl));
  } else if (!ctx->pool->clauses.empty ()) {
    std::uniform_int_distribution<size_t> dist (
        0, ctx->pool->clauses.size () - 1);
    ctx->pool->clauses[dist (*ctx->rng)] = std::move (cl);
  }
  return 0;
}

static Result evaluate_genome (const Genome &g, const Formula &formula,
                               const EvoOptions &opts,
                               const std::vector<GeneSpec> &specs,
                               SharedPool &pool, ActiveSolvers &active,
                               std::atomic<bool> &stop,
                               std::atomic<bool> &gen_abort,
                               double deadline, std::mutex &best_mutex,
                               double &best_unfitness,
                               std::atomic<double> &best_so_far,
                               std::mutex &solution_mutex,
                               kissat *&solution_solver,
                               int &solution_status) {
  Result res;
  res.genome = g;
  kissat *solver = kissat_init ();
  register_solver (active, solver);
  if (stop.load () || gen_abort.load ())
    kissat_terminate (solver);
  apply_options (solver, opts, g, specs);
  TerminationState term_state;
  term_state.stop = &stop;
  term_state.abort = &gen_abort;
  term_state.deadline = deadline;
  kissat_set_terminate (solver, &term_state, terminate_cb);

  if (formula.max_var > 0)
    kissat_reserve (solver, formula.max_var);
  for (int lit : formula.lits)
    kissat_add (solver, lit);
  if (!g.phases.empty ())
    kissat_set_initial_phases (solver, g.phases.data (),
                               (unsigned) g.phases.size ());

  std::mt19937 rng (g.seed ^ 0x9e3779b9U);
  import_shared (solver, formula, pool, opts.share_in, rng);

  if (opts.conflicts_limit >= 0)
    kissat_set_conflict_limit (solver, (unsigned) opts.conflicts_limit);
  if (opts.decisions_limit >= 0)
    kissat_set_decision_limit (solver, (unsigned) opts.decisions_limit);

  const double start = kissat_wall_clock_time ();
  std::atomic<bool> eval_done (false);
  std::thread eval_timer;
  if (opts.eval_time_limit > 0 || deadline > 0) {
    double until = 0.0;
    if (opts.eval_time_limit > 0)
      until = start + opts.eval_time_limit;
    if (deadline > 0 && (until == 0.0 || deadline < until))
      until = deadline;
    eval_timer = std::thread ([&] () {
      for (;;) {
        if (eval_done.load ())
          return;
        const double now = kissat_wall_clock_time ();
        if (now >= until) {
          kissat_terminate (solver);
          return;
        }
        const double remaining = until - now;
        int sleep_ms = (int) (remaining * 1000.0);
        if (sleep_ms > 25)
          sleep_ms = 25;
        if (sleep_ms < 1)
          sleep_ms = 1;
        std::this_thread::sleep_for (
            std::chrono::milliseconds (sleep_ms));
      }
    });
  }
  const int status = kissat_solve (solver);
  const double end = kissat_wall_clock_time ();
  eval_done.store (true);
  if (eval_timer.joinable ())
    eval_timer.join ();
  res.elapsed = end - start;

  res.status = status;
  res.unfitness = 0.0;
  res.evaluated = true;
  res.aborted = gen_abort.load () && status == 0;
  res.remaining_vars = kissat_get_solver_active_variables (solver);
  res.remaining_clauses = kissat_get_solver_active_clauses (solver);
  res.remaining_binary = kissat_get_solver_binary_clauses (solver);

  if (status == 10 || status == 20)
    res.unfitness = 0.0;
  else
    res.unfitness = kissat_get_remaining_unfitness (solver);

  unregister_solver (active, solver);

  bool export_it = false;
  {
    std::lock_guard<std::mutex> lock (best_mutex);
    if (res.unfitness < best_unfitness) {
      best_unfitness = res.unfitness;
      best_so_far.store (best_unfitness, std::memory_order_relaxed);
      res.improved = true;
      export_it = true;
    } else {
      const double tolerance = std::max (1e-9, std::fabs (best_unfitness) * 0.05);
      if (res.unfitness <= best_unfitness + tolerance)
        export_it = true;
    }
  }

  if (export_it) {
    ExportContext ctx;
    ctx.pool = &pool;
    ctx.max_pool = opts.share_pool;
    ctx.rng = &rng;
    kissat_export_shared_clauses (solver, opts.share_max_size,
                                  opts.share_max_glue, opts.share_out,
                                  &ctx, export_shared_clause);
  }

  if (status == 10 || status == 20) {
    {
      std::lock_guard<std::mutex> lock (solution_mutex);
      if (!solution_solver) {
        solution_solver = solver;
        solution_status = status;
      } else {
        kissat_release (solver);
      }
    }
    stop.store (true);
    terminate_active (active);
  } else {
    kissat_release (solver);
  }

  return res;
}

static Genome tournament_select (const std::vector<Result> &results,
                                 std::mt19937 &rng) {
  std::uniform_int_distribution<size_t> dist (0, results.size () - 1);
  const Result *best = nullptr;
  for (int i = 0; i < 3; i++) {
    const Result &cand = results[dist (rng)];
    if (!best || cand.unfitness < best->unfitness)
      best = &cand;
  }
  return best->genome;
}

int main (int argc, char **argv) {
  EvoOptions opts;
  if (!parse_args (argc, argv, opts))
    return 1;

  const unsigned logical_cores = pick_threads ();
  if (!opts.threads)
    opts.threads = logical_cores;
  if (!opts.population)
    opts.population = opts.threads * 4;
  // opts.max_evals == 0 means unlimited evaluations.
  if (!opts.evo_seed)
    opts.evo_seed = (unsigned) std::random_device{} ();

  Formula formula;
  if (!parse_dimacs (opts.input_path.empty () ? nullptr
                                              : opts.input_path.c_str (),
                     formula)) {
    fprintf (stderr, "could not parse input\n");
    return 1;
  }

  if (!opts.quiet) {
    fprintf (stdout,
             "c evo-kissat: clauses %" PRIu64 ", vars %d, "
             "population %u, threads %u\n",
             formula.clauses, formula.max_var, opts.population,
             opts.threads);
  }

  const auto specs = build_gene_specs ();
  const auto base_values = build_base_values (specs, opts.overrides);

  std::mt19937 rng (opts.evo_seed);

  std::vector<Genome> population;
  population.reserve (opts.population);
  for (unsigned i = 0; i < opts.population; i++)
    population.push_back (
        random_genome (specs, base_values, (unsigned) formula.max_var, rng));

  SharedPool pool;
  pool.max_clauses = opts.share_pool;
  ActiveSolvers active;

  std::atomic<bool> stop (false);
  double deadline = 0.0;
  if (opts.time_limit > 0)
    deadline = kissat_wall_clock_time () + opts.time_limit;

  std::mutex best_mutex;
  double best_unfitness = std::numeric_limits<double>::infinity ();
  std::atomic<double> best_so_far (std::numeric_limits<double>::infinity ());

  std::mutex solution_mutex;
  kissat *solution_solver = nullptr;
  int solution_status = 0;

  uint64_t evaluations = 0;
  unsigned generation = 0;

  while (!stop.load () &&
         (opts.max_evals == 0 || evaluations < opts.max_evals)) {
    const double gen_start = kissat_wall_clock_time ();
    std::vector<Result> results (population.size ());
    for (size_t i = 0; i < population.size (); i++)
      results[i].genome = population[i];
    std::atomic<size_t> next (0);
    std::atomic<size_t> completed (0);
    std::atomic<bool> gen_done (false);
    std::atomic<bool> gen_abort (false);
    const unsigned half_cores = std::max (1u, logical_cores / 2);
    const bool allow_cutoff =
        (opts.eval_time_limit == 0) && population.size () >= half_cores;
    std::vector<std::thread> threads;
    threads.reserve (opts.threads);

    std::thread monitor;
    if (!opts.quiet) {
      monitor = std::thread ([&] () {
        double last = kissat_wall_clock_time ();
        while (!gen_done.load ()) {
          std::this_thread::sleep_for (std::chrono::milliseconds (200));
          const double now = kissat_wall_clock_time ();
          if (now - last < 10.0)
            continue;
          last = now;
          const size_t done = completed.load ();
          size_t pool_size = 0;
          {
            std::lock_guard<std::mutex> lock (pool.mutex);
            pool_size =
                pool.units.size () + pool.binaries.size () + pool.clauses.size ();
          }
          const double global_best =
              best_so_far.load (std::memory_order_relaxed);
          printf ("c gen %u progress %zu/%zu global_best_unfit %.6g pool %zu elapsed %.1f\n",
                  generation + 1, done, population.size (), global_best,
                  pool_size, now - gen_start);
          fflush (stdout);
          if (done >= population.size ())
            break;
        }
      });
    }

    for (unsigned t = 0; t < opts.threads; t++) {
      threads.emplace_back ([&] () {
        for (;;) {
          if (stop.load () || gen_abort.load ())
            return;
          if (deadline > 0 && kissat_wall_clock_time () >= deadline) {
            stop.store (true);
            terminate_active (active);
            return;
          }
          size_t idx = next.fetch_add (1);
          if (idx >= population.size ())
            return;
          Result r = evaluate_genome (population[idx], formula, opts,
                                      specs, pool, active, stop, gen_abort,
                                      deadline, best_mutex, best_unfitness,
                                      best_so_far, solution_mutex,
                                      solution_solver, solution_status);
          results[idx] = std::move (r);
          const size_t done = completed.fetch_add (1) + 1;
          if (allow_cutoff) {
            const size_t remaining = population.size () - done;
            if (remaining < half_cores) {
              bool expected = false;
              if (gen_abort.compare_exchange_strong (expected, true))
                terminate_active (active);
            }
          }
        }
      });
    }

    for (auto &th : threads)
      th.join ();
    gen_done.store (true);
    if (monitor.joinable ())
      monitor.join ();

    const size_t evaluated = completed.load ();
    evaluations += evaluated;
    generation++;

    if (!opts.quiet) {
      unsigned sat = 0, unsat = 0, unknown = 0, improved = 0;
      size_t evaluated_count = 0;
      size_t skipped = 0;
      size_t aborted = 0;
      double sum_unfitness = 0.0;
      double best_unfit = std::numeric_limits<double>::infinity ();
      double min_elapsed = 0.0, max_elapsed = 0.0, sum_elapsed = 0.0;
      uint64_t sum_vars = 0;
      uint64_t sum_clauses = 0;
      uint64_t sum_binary = 0;
      for (size_t i = 0; i < results.size (); i++) {
        const Result &r = results[i];
        if (!r.evaluated) {
          skipped++;
          continue;
        }
        if (r.status == 10)
          sat++;
        else if (r.status == 20)
          unsat++;
        else
          unknown++;
        if (r.unfitness < best_unfit)
          best_unfit = r.unfitness;
        sum_unfitness += r.unfitness;
        if (!evaluated_count || r.elapsed < min_elapsed)
          min_elapsed = r.elapsed;
        if (!evaluated_count || r.elapsed > max_elapsed)
          max_elapsed = r.elapsed;
        sum_elapsed += r.elapsed;
        if (r.improved)
          improved++;
        if (r.aborted)
          aborted++;
        sum_vars += r.remaining_vars;
        sum_clauses += r.remaining_clauses;
        sum_binary += r.remaining_binary;
        evaluated_count++;
      }
      const double avg_unfitness =
          evaluated_count ? sum_unfitness / evaluated_count : 0.0;
      const double avg_elapsed =
          evaluated_count ? sum_elapsed / evaluated_count : 0.0;
      const uint64_t avg_vars =
          evaluated_count ? (sum_vars / evaluated_count) : 0;
      const uint64_t avg_clauses =
          evaluated_count ? (sum_clauses / evaluated_count) : 0;
      const uint64_t avg_binary =
          evaluated_count ? (sum_binary / evaluated_count) : 0;
      size_t pool_size = 0;
      {
        std::lock_guard<std::mutex> lock (pool.mutex);
        pool_size =
            pool.units.size () + pool.binaries.size () + pool.clauses.size ();
      }
      const double gen_end = kissat_wall_clock_time ();
      const double global_best =
          best_so_far.load (std::memory_order_relaxed);
      printf ("c gen %u evals %" PRIu64
              " gen_best_unfit %.6g global_best_unfit %.6g avg_unfit %.6g "
              "rem_vars %llu rem_clauses %llu rem_binary %llu "
              "sat %u unsat %u unk %u pool %zu "
              "eval_time min %.3f avg %.3f max %.3f "
              "gen_time %.3f improved %u skipped %zu aborted %zu\n",
              generation, evaluations, best_unfit, global_best, avg_unfitness,
              (unsigned long long) avg_vars,
              (unsigned long long) avg_clauses,
              (unsigned long long) avg_binary, sat, unsat, unknown, pool_size,
              min_elapsed, avg_elapsed, max_elapsed, gen_end - gen_start,
              improved, skipped, aborted);
      fflush (stdout);
    }

    if (stop.load ())
      break;

    std::sort (results.begin (), results.end (),
               [] (const Result &a, const Result &b) {
                 return a.unfitness < b.unfitness;
               });

    population.clear ();
    population.reserve (opts.population);
    population.push_back (results.front ().genome);
    while (population.size () < opts.population) {
      Genome a = tournament_select (results, rng);
      Genome b = tournament_select (results, rng);
      Genome child = crossover (a, b, specs, rng);
      mutate_genome (child, specs, rng);
      population.push_back (std::move (child));
    }
  }

  int status = solution_status ? solution_status : 0;
  if (status == 10)
    printf ("s SATISFIABLE\n");
  else if (status == 20)
    printf ("s UNSATISFIABLE\n");
  else
    printf ("s UNKNOWN\n");

  if (status == 10 && opts.witness && solution_solver)
    print_witness (solution_solver, formula.max_var, opts.partial);
  if (opts.statistics && solution_solver && !opts.quiet) {
    kissat_set_option (solution_solver, "quiet", 0);
    kissat_print_statistics (solution_solver);
  }

  if (solution_solver)
    kissat_release (solution_solver);

  return status ? status : 0;
}
