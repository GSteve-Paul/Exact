#include "basis_pms.h"
#include "pms_small.h"
#include "pms_large.h"
#include "mScip.h"
#include "args.hxx"
#include <sstream>
#include <signal.h>

#include <sys/time.h>
#include <sys/resource.h>

Satlike s;					   // 全局变量PBO
bool solution_printed = false; // 全局变量，用于标记解是否已经输出过

void interrupt(int sig)
{
	if (!solution_printed)
	{
		s.print_best_solution();
		solution_printed = true;
	}

	// if (intsize <= 63)
	// 	s.free_memory_small();
	// else
	// 	s.free_memory_large();

	exit(10);
}

bool parse_options(int argc, char *argv[])
{
	args::ArgumentParser parser(
		"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n PBO -- Northeast normal University(2024)\n",
		"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");

	args::HelpFlag help(parser, "help", "Display this help menu",
						{'h', "help"});
	// args::Group required(parser, "", args::Group::Validators::All);

	args::ValueFlag<std::string> benchmark_file(
		parser, "benchmark", "Path to benchmark", {'f', "file"},
		"normalized-C17.opb");

	args::ValueFlag<int> Seed(parser, "seed", "Seed due to the randomness",
							  {'s', "seed"}, 1);

	args::ValueFlag<int> TimeLim(parser, "Time limitation",
								 "The cut down time in second", {'t', "time"},
								 3600);
	args::ValueFlag<long> MemoryLimit(parser, "memory", "Memory limit in MB", {'m', "memory"}, 500000); // 默认为 500 GB

	args::Flag ScipFlag(parser, "no-s", "The SCIP flag, default use scip", {"no-s"});
// #ifdef USEPRESOLVE
// 	args::ValueFlag<int> PreTimeLimit(parser, "Time Limitation for Presolve", "Set the presolve time limit in seconds", {'p', "presolve-time"}, 200);
// #endif
#ifdef USE_SCIP
	args::ValueFlag<double> ScipLim(parser, "scip-lim", "The scip time limit, default Time / 2", {"scip-lim"});
#endif

	try
	{
		parser.ParseCLI(argc, argv);
	}
	catch (args::Help &)
	{
		std::cout << parser;
		return 0;
	}
	catch (args::ParseError &e)
	{
		std::cerr << e.what() << std::endl;
		std::cerr << parser;
		return 0;
	}
	catch (args::ValidationError &e)
	{
		std::cerr << e.what() << std::endl;
		std::cerr << parser;
		return 0;
	}

	try
	{
		parser.ParseCLI(argc, argv);
	}
	catch (const args::Completion &e)
	{
		std::cout << e.what();
		return 0;
	}
	catch (const args::Help &)
	{
		std::cout << parser;
		return 0;
	}
	catch (const args::ParseError &e)
	{
		std::cerr << e.what() << std::endl;
		std::cerr << parser;
		return 1;
	}

	filename = new char[args::get(benchmark_file).length() + 1];
	std::strcpy(filename, args::get(benchmark_file).c_str());

	seed = args::get(Seed);

	cutoff_time = args::get(TimeLim);
	memory_limit_gb = args::get(MemoryLimit);
	cout << cutoff_time << endl;

#ifdef USE_SCIP
	if (ScipLim)
		opt_scip_cpu = args::get(ScipLim);
	else
		opt_scip_cpu = cutoff_time / 2;
#endif

	if (ScipFlag)
		use_scip = false;
	else
		use_scip = true;

	opt_dec_model = true;

	printf("c Filename:%s, Cutoff_time:%d, memory_limit_gb:%ld\n", basename(filename), cutoff_time, memory_limit_gb);
#ifdef USE_SCIP
	// printf(", %s Scip", use_scip ? "Use" : "Not use");
	if (use_scip)
		printf(", Scip time: %g\n", opt_scip_cpu);
	//;
	else
	{
#endif
		;
		// printf("");
#ifdef USE_SCIP
	}
#endif

	return true;
}

void set_memory_limit(long memory_limit_gb)
{
	const rlim_t kMemoryLimit = memory_limit_gb * 1024L * 1024L; // 30 GB
	struct rlimit rl;
	rl.rlim_cur = kMemoryLimit; // 设置软限制
	rl.rlim_max = kMemoryLimit; // 设置硬限制

	if (setrlimit(RLIMIT_AS, &rl) == -1)
	{
		fprintf(stderr, "c Failed to set memory limit: %s\n", strerror(errno));
	}
}

int main(int argc, char *argv[])
{
	try
	{
		// srand((unsigned)time(NULL));
		start_timing();

		if (!parse_options(argc, argv))
			return 0;

		set_memory_limit(memory_limit_gb); // 设置内存限制

		signal(SIGTERM, interrupt);
		signal(SIGSEGV, interrupt);
		// signal(SIGABRT, interrupt); // 捕获异常终止信号
		// signal(SIGFPE, interrupt);	// 捕获浮点异常信号
		// signal(SIGILL, interrupt);	// 捕获非法指令信号
		signal(SIGINT, interrupt); // 捕获中断信号

		vector<int> init_solution;
		int intsize = s.get_intsize(filename);
#ifdef USEPRESOLVE
		s.use_presolve = false; // 问问对不对
		if (intsize <= 31)
			s.presolve_build(filename);
		else if (intsize < 64)
			s.build_instance_small(filename);
		else
			s.build_instance_large(filename);
#ifdef USE_SCIP
		if (intsize <= 31 && use_scip)
			s.scip_solve();
#endif
		if (intsize <= 31 && s.use_presolve && s.prob.getConstraintMatrix().getNCols() > 0)
			s.local_search_with_decimation_small(init_solution, filename);
		else if (intsize <= 31 && s.use_presolve && s.prob.getConstraintMatrix().getNCols() <= 0)
			s.best_soln_feasible = 1, s.opt_unsat_weight_small = 0, s.opt_realobj_small = 1, s.realobj_small = 0;
		else if (intsize <= 31 && !s.use_presolve)
			s.local_search_with_decimation_small(init_solution, filename);
		else if (intsize > 31 && intsize < 64)
			s.local_search_with_decimation_small(init_solution, filename);
		else if (intsize >= 64)
			s.local_search_with_decimation_large(init_solution, filename);
			// else
			// s.best_soln_feasible = 1, s.opt_unsat_weight_small = 0, s.opt_realobj_small = 1, s.realobj_small = 0;
#else
		if (intsize <= 63)
			s.build_instance_small(filename);
		else
			s.build_instance_large(filename);
#ifdef USE_SCIP
		if (intsize <= 31 && use_scip)
			s.scip_solve();
#endif
		if (intsize <= 63)
			s.local_search_with_decimation_small(init_solution, filename);
		else
			s.local_search_with_decimation_large(init_solution, filename);
#endif
		if (!solution_printed)
		{
			s.print_best_solution();
			solution_printed = true;
		}
		if (intsize <= 63)
			s.free_memory_small();
		else
			s.free_memory_large();
	}
	catch (const std::bad_alloc &e)
	{
		std::cerr << "c Memory allocation failed: " << e.what() << std::endl;
		if (!solution_printed)
		{
			s.print_best_solution();
			solution_printed = true;
		}
		return 1;
	}
	return 0;
}
