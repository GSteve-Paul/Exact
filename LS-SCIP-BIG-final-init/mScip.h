#ifndef _M_SCIP_H_
#define _M_SCIP_H_

#ifdef USE_SCIP
#include "basis_pms.h"
#include <vector>
#include <future>
#include <atomic>
#include <chrono>
#include <thread>
#include <scip/struct_message.h>
#include <limits>

#define MY_SCIP_CALL(x)                         \
    do                                          \
    {                                           \
        SCIP_RETCODE _r_;                       \
        if ((_r_ = (x)) != SCIP_OKAY)           \
        {                                       \
            printf("c SCIP error <%d>\n", _r_); \
            return l_Undef;                     \
        }                                       \
    } while (0)

std::atomic<char>
    opt_finder(OPT_NONE);

struct ScipSolver
{
    SCIP *scip;
    std::vector<SCIP_VAR *> vars;
    std::vector<int> model;
    bool must_be_started;

    ScipSolver() : scip(nullptr), must_be_started(false) {}
};

void Satlike::print_best_solution_OPT() // 传入文件名和seed
{
    if (best_soln_feasible == 1)
    {
#ifdef USEPRESOLVE
        if (!opt_dec_model)
        {
            if (intsize <= 63 && use_presolve)
                postsolve_solution(true, false);
            else
                cout << "o " << realobj_small << endl;
            cout << "s OPTIMUM FOUND" << endl;
        }
        else
        {
            cout << "s SATISFIABLE" << endl;
        }
        if (intsize <= 63 && use_presolve)
            postsolve_solution(false, true);
        else
        {
            cout << "v " << flush;
            for (int i = 1; i <= num_vars; ++i)
            {
                if (best_soln[i] == 0)
                    cout << "-x" << i << " ";
                else
                    cout << 'x' << i << " ";
            }
            cout << endl;
        }
#else
        if (!opt_dec_model)
        {
            cout << "o " << realobj_small << endl;
            cout << "s OPTIMUM FOUND" << endl;
        }
        else
        {
            cout << "s SATISFIABLE" << endl;
        }
        cout << "v " << flush;
        for (int i = 1; i <= num_vars; ++i)
        {
            if (best_soln[i] == 0)
                cout << "-x" << i << " ";
            else
                cout << 'x' << i << " ";
        }
        cout << endl;
#endif
        cout << "c Done " << opt_time << "s" << endl;
    }
    else
        cout << "s UNKNOWN" << endl;
}

int extractNumericPartAsInt(const char *varName)
{
    std::string name(varName);
    std::string numericPart;

    // Iterate through the string and collect all digit characters
    for (char c : name)
    {
        if (std::isdigit(c))
        {
            numericPart += c;
        }
    }

    // Convert the numeric part to an integer
    return numericPart.empty() ? 0 : std::atoi(numericPart.c_str());
}

uint8_t Satlike::scip_solve_async(SCIP *scip, std::vector<SCIP_VAR *> vars)
// uint8_t Satlike::scip_solve_async(SCIP *scip)
{
    uint8_t found_opt = l_Undef;
    SCIP_STATUS status;
    bool obj_limit_applied = false;
    MY_SCIP_CALL(SCIPsetObjIntegral(scip));
    MY_SCIP_CALL(SCIPsolve(scip));
    status = SCIPgetStatus(scip);
    // SCIP_VAR** vars = SCIPgetVars(scip);
    if (status == SCIP_STATUS_OPTIMAL)
    {
        found_opt = l_True;
        SCIP_SOL *sol = SCIPgetBestSol(scip);
        assert(sol != nullptr);
        // MY_SCIP_CALL(SCIPprintSol(scip, sol, nullptr, FALSE));
        for (int x = 0; x < num_vars; x++)
        {
            if (vars[x] != nullptr)
            {
                SCIP_Real v = SCIPgetSolVal(scip, sol, vars[x]);
                // best_soln[extractNumericPartAsInt(SCIPvarGetName(vars[x]))] = int(v > 0.5);
                best_soln[x + 1] = int(v > 0.5);
            }
        }
        // best_soln_feasible = 1;
        if (!verify_sol_small())
            best_soln_feasible = 0;
        else
        {
            best_soln_feasible = 1;
            cal_solution_small();
        }

        // print_best_solution_OPT();
    }
    else if (status == SCIP_STATUS_INFEASIBLE)
    {
        if (obj_limit_applied)
        { // SCIP proved optimality of the last MaxSAT o-value
            return l_True;
        }
        else
        {
            return l_False;
        }
    }
    else // feasible unknown
    {
        SCIP_Real primb = SCIPgetPrimalbound(scip);
        if (!SCIPisInfinity(scip, primb))
        {
            SCIP_SOL *sol = SCIPgetBestSol(scip);
            if (sol != nullptr)
            {
                for (int x = 0; x < num_vars; x++)
                {
                    if (vars[x] != nullptr)
                    {
                        SCIP_Real v = SCIPgetSolVal(scip, sol, vars[x]);
                        best_soln[x + 1] = int(v > 0.5);
                    }
                }
                if (!verify_sol_small())
                    best_soln_feasible = 0;
                else
                {
                    best_soln_feasible = 1;
                    cal_solution_small();

                    // opt_realobj_small = realobj_small;
                    // #ifdef USEPRESOLVE
                    //                     if (intsize <= 63 && use_presolve)
                    //                         postsolve_solution(true, false);
                    //                     else
                    //                     {
                    // #endif
                    // if (realobj_small < opt_realobj_small)
                    // {
                    //     printf("o %lld\n", realobj_small);
                    //     opt_realobj_small = realobj_small;
                    // }
                    // #ifdef USEPRESOLVE
                    //                     }
                    // #endif
                }
            }
        }
    }

    // release SCIP vars
    for (auto v : vars)
        if (v != nullptr)
            MY_SCIP_CALL(SCIPreleaseVar(scip, &v));
    vars.clear();
    MY_SCIP_CALL(SCIPfree(&scip));
    // for(int i = 1; i <= num_vars; i++) printf("%s%d ", best_soln[i] ? "" : "-", i);
    // printf("\n");
    return found_opt;
}

uint8_t Satlike::scip_solve()
{

    int sat_orig_cls = num_hclauses;
    int sat_orig_vars = num_vars;
    if (opt_scip_cpu == 0)
        opt_scip_cpu = 1800;

    if ((sat_orig_cls >= 600000 || num_sclauses >= 100000))
        return l_Undef;

    // printf("c Using SCIP solver, version %.1f.%d, https://www.scipopt.org\n",
    //        SCIPversion(), SCIPtechVersion());

    // 1. create scip context object
    SCIP *scip = nullptr;
    MY_SCIP_CALL(SCIPcreate(&scip));
    MY_SCIP_CALL(SCIPincludeDefaultPlugins(scip));
    char *base = nullptr;
    MY_SCIP_CALL(SCIPcreateProbBasic(scip, (base != nullptr ? base : "IPAMIR of UWrMaxSat")));
    MY_SCIP_CALL(SCIPsetEmphasis(scip, SCIP_PARAMEMPHASIS_DEFAULT, TRUE));
    if (opt_scip_cpu > 0)
        MY_SCIP_CALL(SCIPsetRealParam(scip, "limits/time", opt_scip_cpu));
    MY_SCIP_CALL(SCIPsetIntParam(scip, "display/verblevel", 0));
    // MY_SCIP_CALL(SCIPreadProb(scip, filename, nullptr) );  // 读取 OPB 文件

    // 2. create variable(include relax)
    std::vector<SCIP_VAR *> vars(sat_orig_vars, nullptr);
    for (int i = 0; i < num_vars; i++)
    {
        SCIP_VAR *scip_var = vars[i];
        if (scip_var == nullptr)
        {
            std::string name = "x" + std::to_string(i);
            SCIP_Real lb = 0, ub = 1;
            MY_SCIP_CALL(SCIPcreateVarBasic(scip, &scip_var, name.c_str(), lb, ub, 0, SCIP_VARTYPE_BINARY));
            MY_SCIP_CALL(SCIPaddVar(scip, scip_var));
            vars[i] = scip_var;
        }
    }

    // 3. add constraint
    long long w;
    for (int i = 0; i < num_hclauses; i++)
    {
        std::string cons_name = "cons" + std::to_string(i);
        SCIP_CONS *cons = nullptr;
        MY_SCIP_CALL(SCIPcreateConsBasicLinear(scip, &cons, cons_name.c_str(), 0, nullptr, nullptr, 0, SCIPinfinity(scip)));
        w = 0;
        for (int j = 0; j < clause_lit_count[hard_clause_num_index[i]]; j++)
        {
            MY_SCIP_CALL(SCIPaddCoefLinear(scip, cons, vars[clause_lit_small[hard_clause_num_index[i]][j].var_num - 1],
                                           clause_lit_small[hard_clause_num_index[i]][j].sense ? clause_lit_small[hard_clause_num_index[i]][j].weight : -clause_lit_small[hard_clause_num_index[i]][j].weight));
            w += clause_lit_small[hard_clause_num_index[i]][j].sense ? 0 : -clause_lit_small[hard_clause_num_index[i]][j].weight;
        }
        MY_SCIP_CALL(SCIPchgLhsLinear(scip, cons, clause_true_lit_thres_small[hard_clause_num_index[i]] + w));
        MY_SCIP_CALL(SCIPaddCons(scip, cons));
        MY_SCIP_CALL(SCIPreleaseCons(scip, &cons));
    }

    // 4. set objective
    for (int i = 0; i < num_sclauses; i++)
    {
        for (int j = 0; j < clause_lit_count[soft_clause_num_index[i]]; j++)
        {
            SCIPchgVarObj(scip, vars[clause_lit_small[soft_clause_num_index[i]][j].var_num - 1],
                          clause_lit_small[soft_clause_num_index[i]][j].sense ? -org_clause_weight_small[soft_clause_num_index[i]] : org_clause_weight_small[soft_clause_num_index[i]]);
        }
    }

    // 5. do solve
    // MY_SCIP_CALL((SCIPwriteOrigProblem(scip, "1.lp", nullptr, FALSE)));
    // MY_SCIP_CALL((SCIPwriteTransProblem(scip, "2.lp", nullptr, FALSE)));
    // printf("c Starting SCIP solver (with time-limit = %.0fs) ...\n", opt_scip_cpu);
    /*    MY_SCIP_CALL( SCIPsolve(scip) );  // 开始求解
        SCIP_SOL* sol = SCIPgetBestSol(scip);  // 获取最优解
    if (sol != nullptr) {
        double obj = SCIPgetSolOrigObj(scip, sol);
        std::cout << "Solution found with objective value: " << obj << std::endl;
    } else {
        std::cout << "No solution found." << std::endl;
    }*/

    return scip_solve_async(scip, std::move(vars));
    // return scip_solve_async(scip);
    // return l_True;
}

#endif
#endif
