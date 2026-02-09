#include "test.h"

#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static void test_evo_kissat_f2000 (void) {
  const char *path = "./evo-kissat";
  const char *cnf = "../test/cnf/f2000.cnf";
  const char *args[] = {
      path,
      "-q",
      "--time=3",
      "--evo-evals=32",
      "--evo-pop=16",
      "--evo-threads=4",
      "--conflicts=500",
      cnf,
      0,
  };

  pid_t child = fork ();
  if (child < 0)
    FATAL ("failed to fork evo-kissat");
  if (!child) {
    execv (path, (char *const *) args);
    _exit (1);
  }

  int wstatus = 0;
  pid_t pid = waitpid (child, &wstatus, 0);
  if (pid != child)
    FATAL ("failed to wait for evo-kissat");
  if (WIFSIGNALED (wstatus)) {
    const int sig = WTERMSIG (wstatus);
    FATAL ("evo-kissat terminated by signal %d", sig);
  }
  if (!WIFEXITED (wstatus))
    FATAL ("evo-kissat did not exit normally");

  const int status = WEXITSTATUS (wstatus);
  if (status != 0 && status != 10 && status != 20)
    FATAL ("unexpected exit status %d from evo-kissat", status);
}

void tissat_schedule_evo (void) { SCHEDULE_FUNCTION (test_evo_kissat_f2000); }
