#ifndef _BASIS_PMS_H_
#define _BASIS_PMS_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <queue>
#include <stdio.h>
#include <stdlib.h>
#include <sys/times.h> //these two h files are for timing in linux
#include <unistd.h>

#ifdef USEPRESOLVE
#include <papilo/core/Problem.hpp>
#include <papilo/core/ConstraintMatrix.hpp>
#include <papilo/misc/MultiPrecision.hpp>
#include <papilo/core/ProblemBuilder.hpp>
#include <papilo/core/Presolve.hpp>
#include <papilo/misc/Wrappers.hpp>
#include <papilo/misc/Vec.hpp>
#endif

#ifdef USE_SCIP
#include <scip/scip.h>
#include <scip/scipdefplugins.h>
#endif

#include "Int.h"

using namespace std;

#define mypop(stack) stack[--stack##_fill_pointer]
#define mypush(item, stack) stack[stack##_fill_pointer++] = item

#ifdef USE_SCIP
enum OptFinder
{
	OPT_NONE,
	OPT_SCIP,
	OPT_MSAT
};
#define l_True (uint8_t)0
#define l_False (uint8_t)1
#define l_Undef (uint8_t)2
double opt_scip_cpu;
#endif

const float MY_RAND_MAX_FLOAT = 10000000.0;
const int MY_RAND_MAX_INT = 10000000;
const float BASIC_SCALE = 0.0000001; // 1.0f/MY_RAND_MAX_FLOAT;

int seed;
bool use_scip;
char *filename;
bool opt_dec_model;
int cutoff_time;
long memory_limit_gb;
// int presolveTimeLimit;

// Define a data structure for a literal.
struct lit_small
{
	int clause_num; // clause num, begin with 0
	int var_num;	// variable num, begin with 1
	bool sense;		// is 1 for true literals, 0 for false literals.
	long long weight;
};

struct lit_large
{
	int clause_num; // clause num, begin with 0
	int var_num;	// variable num, begin with 1
	bool sense;		// is 1 for true literals, 0 for false literals.
	Int weight;
};

static struct tms start_time;
static double get_runtime()
{
	struct tms stop;
	times(&stop);
	return (double)(stop.tms_utime - start_time.tms_utime + stop.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK);
}
static void start_timing()
{
	times(&start_time);
}

class Satlike
{
public:
	/***********non-algorithmic information ****************/
	// int problem_weighted;
	// int partial; // 1 if the instance has hard clauses, and 0 otherwise.
	// size of the instance
	int num_vars;	 // var index from 1 to num_vars
	int num_clauses; // clause index from 0 to num_clauses-1
	int num_hclauses;
	int num_sclauses;
	int num_equal;

	// steps and time
	int tries;
	int max_tries;
	unsigned int max_flips;
	// unsigned int max_non_improve_flip;
	unsigned int step;

	// int print_time;
	double opt_time;

	/*sumnegmincoeff*/
	long long sumneg_min_small;
	long long realobj_small;
	Int sumneg_min_large;
	Int realobj_large;
	long long opt_realobj_small;

	/**********hhscore_small**********/
	double *hhscore_small;
	Int *hhscore_large;
	long long *clause_max_weight_small;
	long long *clause_total_sum_small;
	long long *gap1_small;
	Int *clause_max_weight_large;
	Int *clause_total_sum_large;
	Int *gap1_large;

	/*fps*/
	double *score_baocun_small;
	Int *score_baocun_large;
	double *sscore_baocun_small;
	Int *sscore_baocun_large;
	double *hhscore_baocun_small;
	Int *hhscore_baocun_large;
	double *score2_small;
	Int *score2_large;
	double *sscore2_small;
	Int *sscore2_large;
	double *hhscore2_small;
	Int *hhscore2_large;
	int *goodvar_stack2;
	int goodvar_stack2_num;
	int best_flip_neighbor;
	long long *sat_count2_small;
	Int *sat_count2_large;

	/*turb_small*/
	int *turb_hardunsat_stack;
	int *var_mark;
	int *is_selected_clauses;
	int *selected_var;
	int *turb_best_soln;
	int selected_var_num;

	/*NuPBO*/
	double *tune_soft_clause_weight_small; // soft-smooth
	Int *tune_soft_clause_weight_large;
	double *tuned_degree_unit_weight_small = NULL; // hard-smooth
	Int *tuned_degree_unit_weight_large = NULL;
	int *soft_clause_num_index = NULL;
	int *hard_clause_num_index = NULL;
	double *avg_clause_coe_small;
	Int *avg_clause_coe_large;

	/*MAB-s*/
	int backward_step; // reward delay steps
	double gamma;	   // reward discount factor
	double lambda;	   // exploration bias parameter
	int ArmNum;		   // number of sampled arms
	int current_index;
	int local_times;
	long long pre_unsat_weight_small;
	Int pre_unsat_weight_large;
	double max_clause_score_small;
	Int max_clause_score_large;
	int if_exceed;
	int tabu_step;
	double *clause_score_small;
	Int *clause_score_large;
	int *selected_clauses;
	int *selected_times;
	int *sampled_clauses;

	/*MAB-h*/
	int *selected_clauses_hard;
	double *clause_hard_score_small;
	Int *clause_hard_score_large;
	int *selected_times_hard;
	int *sampled_clauses_hard;
	int local_times_hard;
	int pre_unsat_hard_nb;
	long long pre_hard_unsat_weight_small;
	Int pre_hard_unsat_weight_large;
	long long hard_unsat_weight_small;
	Int hard_unsat_weight_large;
	int if_exceed_hard;

	/**********end non-algorithmic information*****************/
	/* literal arrays */
	lit_small **var_lit_small; // var_lit_small[i][j] means the j'th literal of var i.
	lit_large **var_lit_large;
	int *var_lit_count;			  // amount of literals of each var
	lit_small **clause_lit_small; // clause_lit_small[i][j] means the j'th literal of clause i.
	lit_large **clause_lit_large;
	int *clause_lit_count; // amount of literals in each clause
	long long *clause_true_lit_thres_small;
	Int *clause_true_lit_thres_large;
	int *clause_visied_times; // wyy

	/* Information about the variables. */
	double *score_small;
	Int *score_large;
	double *sscore_small;
	Int *sscore_large;
	long long *time_stamp;
	int **var_neighbor;
	int *var_neighbor_count;
	int *neighbor_flag;
	int *temp_neighbor;
	/* Information about the clauses */
	long long top_clause_weight_small;
	Int top_clause_weight_large;
	long long *org_clause_weight_small;
	Int *org_clause_weight_large;
	long long total_soft_weight_small;
	Int total_soft_weight_large;
	long long *clause_weight_small;
	Int *clause_weight_large;
	double *unit_weight_small;
	Int *unit_weight_large;
	long long *org_unit_weight_small;
	Int *org_unit_weight_large;
	long long ave_soft_weight_small;
	Int ave_soft_weight_large;
	long long ave_hard_weight_small;
	Int ave_hard_weight_large;
	long long inc_hard_weight_small;
	Int inc_hard_weight_large;

	long long *sat_count_small;
	Int *sat_count_large;
	// int *sat_var;
	// long long *clause_selected_count;
	// int *best_soft_clause;

	// original unit clause stack
	// lit_small *unit_clause;
	// int unit_clause_count;

	// unsat_small clauses stack
	int *hardunsat_stack;		   // store the unsat_small clause number
	int *index_in_hardunsat_stack; // which position is a clause in the unsat_stack
	int hardunsat_stack_fill_pointer;

	int *softunsat_stack;		   // store the unsat_small clause number
	int *index_in_softunsat_stack; // which position is a clause in the unsat_stack
	int softunsat_stack_fill_pointer;

	// variables in unsat_small clauses
	int *unsatvar_stack;
	int unsatvar_stack_fill_pointer;
	int *index_in_unsatvar_stack;
	// int *unsat_app_count; // a varible appears in how many unsat_small clauses

	// good decreasing variables (dscore>0 and confchange=1)
	int *goodvar_stack;
	int goodvar_stack_fill_pointer;
	int *already_in_goodvar_stack;

	/* wyy */

	/* Information about solution */
	int *cur_soln; // the current solution, with 1's for True variables, and 0's for False variables
	int *best_soln;
	int *local_opt_soln;
	int best_soln_feasible; // when find a feasible solution, this is marked as 1.
	// int local_soln_feasible;
	int hard_unsat_nb;
	long long soft_unsat_weight_small;
	Int soft_unsat_weight_large;
	long long opt_unsat_weight_small;
	Int opt_unsat_weight_large;
	// long long local_opt_unsat_weight;

	// clause weighting
	// int *large_weight_clauses;
	// int large_weight_clauses_count;
	// int large_clause_count_threshold;

	// int *soft_large_weight_clauses;
	// int *already_in_soft_large_weight_stack;
	// int soft_large_weight_clauses_count;
	// int soft_large_clause_count_threshold;

	// tem data structure used in algorithm
	// int *best_array;
	// int best_count;
	// int *temp_lit;

	// parameters used in algorithm
	float rwprob;
	float rdprob;
	// float smooth_probability;
	int hd_count_threshold;
	int h_inc;

	int intsize;
	// int softclause_weight_threshold;

#ifdef USEPRESOLVE
	papilo::ProblemBuilder<double> probBuilder;
	papilo::Presolve<double> presolver;
	papilo::PresolveResult<double> result;
	papilo::Problem<double> prob;
#endif

	// function used in algorithm
	void build_neighbor_relation_small();
	void build_neighbor_relation_large();
	void allocate_memory_small();
	void allocate_memory_large();
	bool verify_sol_small();
	bool verify_sol_large();
	void increase_weights_small();
	void increase_weights_large();
	void smooth_weights_small();
	void smooth_weights_large();
	void update_clause_weights_small();
	void update_clause_weights_large();
	void unsat_small(int clause);
	void unsat_large(int clause);
	void sat_small(int clause);
	void sat_large(int clause);
	void init_small(vector<int> &init_solution);
	void init_large(vector<int> &init_solution);
	void flip_small(int flipvar);
	void flip_large(int flipvar);
	void flip_fps_small(int flipvar); // fps
	void flip_fps_large(int flipvar);
	void update_goodvarstack1_small(int flipvar);
	void update_goodvarstack1_large(int flipvar);
	void update_goodvarstack2_small(int flipvar);
	void update_goodvarstack2_large(int flipvar);
	void update_goodvarstack12_small(int flipvar); // fps
	void update_goodvarstack12_large(int flipvar);
	int pick_var_small();
	int pick_var_large();
	void pick_vars_small(); // fps
	void pick_vars_large();
	void settings_small();
	void settings_large();
	void turb_small(); // turb_small
	void turb_large();
	int turb_pick_var_small(int last_flip_var); // turb_small
	int turb_pick_var_large(int last_flip_var);
	void init_turb_small(); // turb_small
	void init_turb_large();
	int pick_softc_small(); // MAB
	int pick_softc_large();
	void update_clause_scores_small(long long s); // MAB
	void update_clause_scores_large(Int s);
	int pick_hardc_small(); // MAB-h
	int pick_hardc_large();
	void update_clause_scores_hard_small(long long s); // MSB-h
	void update_clause_scores_hard_large(Int s);

public:
	Satlike();
	int get_intsize(char *filename);
#ifdef USE_SCIP
	bool *equal_cons;
	void print_best_solution_OPT();
	uint8_t scip_solve_async(SCIP *scip, std::vector<SCIP_VAR *> vars);
	// uint8_t scip_solve_async(SCIP *scip);
	uint8_t scip_solve();
#endif
#ifdef USEPRESOLVE
	bool use_presolve;
	void presolve_build(char *filename);
	void postsolve_solution(bool flag_value, bool flag_solution);
#endif
	void build_instance_small(char *filename);
	void build_instance_large(char *filename);
	void local_search_small(vector<int> &init_solution);
	void local_search_large(vector<int> &init_solution);
	void local_search_with_decimation_small(vector<int> &init_solution, char *inputfile);
	void local_search_with_decimation_large(vector<int> &init_solution, char *inputfile);
	void simple_print_small();
	void simple_print_large();
	void print_best_solution(); // 传入测试名和seed
	void free_memory_small();
	void free_memory_large();
	void check_new_score_small();
	void check_new_score_large();
	void check_softunsat_weight_small();
	void check_softunsat_weight_large();
	void cal_solution_small();
	void cal_solution_large();
	// void get_obj(string opb_file_name); // new added
};

#endif
