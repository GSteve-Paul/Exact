#ifndef _PMS_S_H_
#define _PMS_S_H_

#include "basis_pms.h"
#include <algorithm>
#include <cmath>
#include <iomanip>
#include <sstream>

Satlike::Satlike()
{
  sumneg_min_small = 0;
  // realobj_small = 0;

  // size of the instance
  num_vars = 0;    // var index from 1 to num_vars
  num_clauses = 0; // clause index from 0 to num_clauses-1
  num_hclauses = 0;
  num_sclauses = 0;
  num_equal = 0;

  // realobj_small = INT64_MAX;
}

void Satlike::settings_small()
{
  // steps
  max_tries = 100000000;
  // max_tries = 4;
  max_flips = 200000000;
  // max_flips = 10000;
  // max_flips = 30;
  // max_non_improve_flip = 10000000;

  // large_clause_count_threshold = 0;
  // soft_large_clause_count_threshold = 0;

  rdprob = 0.01;
  hd_count_threshold = 15;
  rwprob = 0.1;
  // smooth_probability = 0.01;

  h_inc = 1;
  // softclause_weight_threshold = 1;

  gamma = 0.9;
  lambda = 1.0;

  if (num_clauses <= 20)
  {
    ArmNum = num_clauses;
    backward_step = num_clauses; // MAB
  }
  else
  {
    ArmNum = 20;
    backward_step = 21; // MAB
  }
  max_clause_score_small = 1000;

  if (num_vars > 2000)
  {
    rdprob = 0.01;
    hd_count_threshold = 15; // 50
    rwprob = 0.1;
    // smooth_probability = 0.0000001;
  }
}

void Satlike::allocate_memory_small()
{
  int malloc_var_length = num_vars + 10;
  int malloc_clause_length = num_clauses + 10;

  // unit_clause = new lit_small[malloc_clause_length];

  var_lit_small = new lit_small *[malloc_var_length];
  var_lit_count = new int[malloc_var_length];
  clause_lit_small = new lit_small *[malloc_clause_length];
  clause_lit_count = new int[malloc_clause_length];
  clause_true_lit_thres_small = new long long[malloc_clause_length];
  clause_visied_times = new int[malloc_clause_length]; // wyy
  equal_cons = new bool[malloc_clause_length];
  for (int i = 0; i < malloc_clause_length; i++)
    equal_cons[i] = false;

  hhscore_small = new double[malloc_var_length]; // hhscore_small
  clause_max_weight_small =
      new long long[malloc_clause_length];                      // 每个子句中的最大系数
  clause_total_sum_small = new long long[malloc_clause_length]; // 每个子句系数之和
  gap1_small = new long long[malloc_clause_length];             // gap1_small
  // best_soln_300 = new int[malloc_var_length];
  // best_soln_1800 = new int[malloc_var_length];
  // opb = new long long[malloc_var_length];

  turb_hardunsat_stack = new int[malloc_clause_length]; // turb_small
  var_mark = new int[malloc_var_length];
  is_selected_clauses = new int[malloc_clause_length];
  selected_var = new int[malloc_var_length];
  turb_best_soln = new int[malloc_var_length];

  score_baocun_small = new double[10]; // fps
  sscore_baocun_small = new double[10];
  hhscore_baocun_small = new double[10];
  score2_small = new double[malloc_var_length];
  sscore2_small = new double[malloc_var_length];
  hhscore2_small = new double[malloc_var_length];
  sat_count2_small = new long long[malloc_clause_length];
  goodvar_stack2 = new int[malloc_var_length];

  clause_score_small = new double[malloc_clause_length]; // MAB-s
  selected_clauses = new int[malloc_clause_length];
  selected_times = new int[malloc_clause_length];
  sampled_clauses = new int[malloc_clause_length];

  selected_clauses_hard = new int[malloc_clause_length]; // MAB-h
  clause_hard_score_small = new double[malloc_clause_length];
  selected_times_hard = new int[malloc_clause_length];
  sampled_clauses_hard = new int[malloc_clause_length];

  tune_soft_clause_weight_small = new double[malloc_clause_length]; // NuPBO
  tuned_degree_unit_weight_small = new double[malloc_clause_length];
  soft_clause_num_index = new int[malloc_clause_length];
  hard_clause_num_index = new int[malloc_clause_length];
  avg_clause_coe_small = new double[malloc_clause_length]();

  score_small = new double[malloc_var_length];
  sscore_small = new double[malloc_var_length];
  // oscore = new long long[malloc_var_length];
  var_neighbor = new int *[malloc_var_length];
  var_neighbor_count = new int[malloc_var_length];
  time_stamp = new long long[malloc_var_length];
  neighbor_flag = new int[malloc_var_length];
  temp_neighbor = new int[malloc_var_length];

  org_clause_weight_small = new long long[malloc_clause_length];
  clause_weight_small = new long long[malloc_clause_length];
  unit_weight_small = new double[malloc_clause_length];
  org_unit_weight_small = new long long[malloc_clause_length];
  sat_count_small = new long long[malloc_clause_length];
  // sat_var = new int[malloc_clause_length];
  // clause_selected_count = new long long[malloc_clause_length];
  // best_soft_clause = new int[malloc_clause_length];

  hardunsat_stack = new int[malloc_clause_length];
  index_in_hardunsat_stack = new int[malloc_clause_length];
  softunsat_stack = new int[malloc_clause_length];
  index_in_softunsat_stack = new int[malloc_clause_length];

  unsatvar_stack = new int[malloc_var_length];
  index_in_unsatvar_stack = new int[malloc_var_length];
  // unsat_app_count = new int[malloc_var_length];

  goodvar_stack = new int[malloc_var_length];
  already_in_goodvar_stack = new int[malloc_var_length];

  cur_soln = new int[malloc_var_length];
  best_soln = new int[malloc_var_length];
  // local_opt_soln = new int[malloc_var_length];

  // large_weight_clauses = new int[malloc_clause_length];
  // soft_large_weight_clauses = new int[malloc_clause_length];
  // already_in_soft_large_weight_stack = new int[malloc_clause_length];

  // best_array = new int[malloc_var_length];
  // temp_lit = new int[malloc_var_length];
}

void Satlike::free_memory_small()
{
  int i;
  for (i = 0; i < num_clauses; i++)
    delete[] clause_lit_small[i];

  for (i = 1; i <= num_vars; ++i)
  {
    delete[] var_lit_small[i];
    delete[] var_neighbor[i];
  }
  /*hhscore_small*/
  delete[] hhscore_small;
  delete[] clause_max_weight_small;
  delete[] clause_total_sum_small;
  delete[] gap1_small;
  // delete[] best_soln_300;
  // delete[] best_soln_1800;
  // delete[] opb;
  //  delete[] same_big_score;
  /*hhscore_small*/

  delete[] turb_hardunsat_stack; // turb_small
  delete[] var_mark;
  delete[] is_selected_clauses;
  delete[] selected_var;
  delete[] turb_best_soln;

  delete[] score_baocun_small; // fps
  delete[] sscore_baocun_small;
  delete[] hhscore_baocun_small;
  delete[] score2_small;
  delete[] sscore2_small;
  delete[] hhscore2_small;
  delete[] sat_count2_small;
  delete[] goodvar_stack2;

  delete[] tune_soft_clause_weight_small; // NuPBO
  delete[] tuned_degree_unit_weight_small;
  delete[] soft_clause_num_index;
  delete[] hard_clause_num_index;
  delete[] avg_clause_coe_small;

  delete[] clause_score_small; // MAB-s
  delete[] selected_clauses;
  delete[] selected_times;
  delete[] sampled_clauses;

  delete[] selected_clauses_hard; // MAB-h
  delete[] clause_hard_score_small;
  delete[] selected_times_hard;
  delete[] sampled_clauses_hard;

  delete[] var_lit_small;
  delete[] var_lit_count;
  delete[] clause_lit_small;
  delete[] clause_lit_count;
  delete[] clause_true_lit_thres_small;
  delete[] clause_visied_times;

  delete[] score_small;
  // delete[] oscore;
  delete[] sscore_small;
  delete[] var_neighbor;
  delete[] var_neighbor_count;
  delete[] time_stamp;
  delete[] neighbor_flag;
  delete[] temp_neighbor;

  delete[] org_clause_weight_small;
  delete[] clause_weight_small;
  delete[] unit_weight_small;
  delete[] org_unit_weight_small;
  delete[] sat_count_small;
  // delete[] sat_var;
  // delete[] clause_selected_count;
  // delete[] best_soft_clause;

  delete[] hardunsat_stack;
  delete[] index_in_hardunsat_stack;
  delete[] softunsat_stack;
  delete[] index_in_softunsat_stack;

  delete[] unsatvar_stack;
  delete[] index_in_unsatvar_stack;
  // delete[] unsat_app_count;

  delete[] goodvar_stack;
  delete[] already_in_goodvar_stack;

  // delete [] fix;
  delete[] cur_soln;
  delete[] best_soln;
  // delete[] local_opt_soln;

  // delete[] large_weight_clauses;
  // delete[] soft_large_weight_clauses;
  // delete[] already_in_soft_large_weight_stack;

  // delete[] best_array;
  // delete[] temp_lit;
}

void Satlike::build_neighbor_relation_small()
{
  int i, j, count;
  int v, c, n;
  int temp_neighbor_count;

  for (v = 1; v <= num_vars; ++v)
  {
    neighbor_flag[v] = 1;
    temp_neighbor_count = 0;

    for (i = 0; i < var_lit_count[v]; ++i)
    {
      c = var_lit_small[v][i].clause_num;
      for (j = 0; j < clause_lit_count[c]; ++j)
      {
        n = clause_lit_small[c][j].var_num;
        if (neighbor_flag[n] != 1)
        {
          neighbor_flag[n] = 1;
          temp_neighbor[temp_neighbor_count++] = n;
        }
      }
    }

    neighbor_flag[v] = 0;

    var_neighbor[v] = new int[temp_neighbor_count];
    var_neighbor_count[v] = temp_neighbor_count;

    count = 0;
    for (i = 0; i < temp_neighbor_count; i++)
    {
      var_neighbor[v][count++] = temp_neighbor[i];
      neighbor_flag[temp_neighbor[i]] = 0;
    }
  }
}

int Satlike::get_intsize(char *filename)
{
  std::ifstream file(filename, std::ifstream::in);
  if (file.fail())
  {
    file.close();
    throw "c " + std::string(filename) + " does not exist!";
    cout << "s UNSUPPORTED" << endl;
    cout << "c the input filename " << filename
         << " is invalid, please input the correct filename." << endl;
    exit(-1);
  }

  for (int i = 0; i < 9; ++i)
  {
    std::string temp;
    file >> temp;
    if (i == 8)
      intsize = stoi(temp);
  }
  file.close();
  return intsize;
}

void Satlike::build_instance_small(char *filename)
{
  printf("c Not use presolve\n");
  int i, v, c;
  int num_hc;
  int num_intsize;

  std::string s;
  // int     temp_lit[MAX_VARS];

  std::ifstream file(filename, std::ifstream::in);
  if (file.fail())
  {
    file.close();
    throw "c " + std::string(filename) + " does not exist!";
    cout << "s UNSUPPORTED" << endl;
    cout << "c the input filename " << filename
         << " is invalid, please input the correct filename." << endl;
    exit(-1);
  }

  for (int i = 0; i < 9; ++i)
  {
    std::string temp;
    file >> temp;
    if (i == 2)
      num_vars = std::stoi(temp);
    if (i == 4)
      num_hc = std::stoi(temp);
    if (i == 6)
      num_equal = std::stoi(temp);
    if (i == 8)
      if (stoi(temp) > 63)
      {
        printf("s UNSUPPORTED\n");
        printf("c intsize > 64\n");
        exit(0);
      }
  }
  std::string commentLineTemp;
  bool loadingObj = false;
  long long int coeff;
  int newcol = 0;
  num_hclauses = num_hc + num_equal;

  num_sclauses = 0; // 软子句数目为0
  sumneg_min_small = 0;
  top_clause_weight_small = 0; // 最高子句权重为0
  while (file >> s)
  {
    if (s == "*" || s[0] == '*')
      std::getline(file, commentLineTemp);
    // Load objective function
    else if (s == "min:")
      loadingObj = true, opt_dec_model = false;
    else if (s == ";")
    {
      loadingObj = false;
    }
    else if (loadingObj)
    {
      if (s[0] == '-' || s[0] == '+' || isdigit(s[0]))
        coeff = std::stoll(s);
      else
      {
        if (coeff > 0)
          top_clause_weight_small += coeff; // top_clause_weight_small = 0 + (+1)
        else
        {
          top_clause_weight_small += (-coeff); // top_clause_weight_small = 0 - (-1)
          sumneg_min_small += (-coeff);
        }
        ++num_sclauses;
      }
    }
    else
    {
      file.close();
      file.open(filename, std::ifstream::in);
      break;
    }
  }

  top_clause_weight_small = top_clause_weight_small + 1;

  num_clauses = num_hclauses + num_sclauses;

  allocate_memory_small(); // 加入了hhscore hard+soft+equal+10

  for (c = 0; c < num_clauses; c++)
  {
    clause_lit_count[c] = 0;
    clause_true_lit_thres_small[c] = 1;
    clause_lit_small[c] = NULL;
  }

  for (v = 1; v <= num_vars; ++v)
  {
    var_lit_count[v] = 0;
    var_lit_small[v] = NULL;
    var_neighbor[v] = NULL;
  }

  long long int *temp_weight = new long long int[num_vars + 10];
  int *temp_lit = new int[num_vars + 10]; // modify local
  // T cur_weight;
  string symbol;
  long long int degree;
  total_soft_weight_small = 0;

  // 处理负系数
  long long int negsum = 0;

  c = 0;

  while (file >> s)
  {
    // Handle coefficient case
    if (s[0] == '+' || s[0] == '-' || isdigit(s[0]))
      coeff = std::stoll(s);
    // Handle bound
    else if (s == ">=" || s == "=")
    {
      symbol = s;
      file >> s;
      temp_weight[clause_lit_count[c]] = 0;
      temp_lit[clause_lit_count[c]] = 0;
      degree = std::stoll(s);
      org_clause_weight_small[c] = top_clause_weight_small;
      int c_equal = 0;
      int c_more = c;
      long long int sum = 0;
      long long int equal_degree = 0;

      long long int equal_temp_weight[clause_lit_count[c] + 10] = {0}; // modify
      int equal_temp_lit[clause_lit_count[c] + 10] = {0};

      if (symbol == "=")
      {
        equal_cons[c] = true;
        c_more = c + 1;
        i = 0;
        sum = 0;

        while (temp_weight[i] != 0)
        {
          equal_temp_weight[i] = temp_weight[i];
          sum += temp_weight[i];
          i++;
        }
        equal_temp_weight[i] = 0;

        i = 0;
        while (temp_lit[i] != 0)
        {
          equal_temp_lit[i] = -temp_lit[i];
          i++;
        }
        equal_temp_lit[i] = 0;

        clause_lit_count[c_more] = clause_lit_count[c];
        equal_degree = sum - degree;
        org_clause_weight_small[c_more] = top_clause_weight_small;
      }

      negsum = 0;
      i = 0;
      while (temp_weight[i] != 0)
      {
        if (temp_weight[i] < 0)
        {
          negsum += -temp_weight[i];
          temp_weight[i] = -temp_weight[i];
          temp_lit[i] = -temp_lit[i];
        }
        i++;
      }
      degree += negsum;
      clause_true_lit_thres_small[c] = degree;
      if (symbol == "=")
      {
        negsum = 0;
        i = 0;
        while (equal_temp_weight[i] != 0)
        {
          if (equal_temp_weight[i] < 0)
          {
            negsum += -equal_temp_weight[i];
            equal_temp_weight[i] = -equal_temp_weight[i];
            equal_temp_lit[i] = -equal_temp_lit[i];
          }
          i++;
        }
        equal_degree += negsum;
        clause_true_lit_thres_small[c_more] = equal_degree;
      }

      long long int max_weight = 0; // find max_weight
      clause_lit_small[c] = new lit_small[clause_lit_count[c] + 1];

      for (i = 0; i < clause_lit_count[c]; ++i)
      {
        clause_lit_small[c][i].clause_num = c;
        clause_lit_small[c][i].var_num = abs(temp_lit[i]);
        clause_lit_small[c][i].weight = temp_weight[i];
        if (temp_weight[i] > max_weight)
          max_weight = temp_weight[i]; // max_weight
        avg_clause_coe_small[c] += double(clause_lit_small[c][i].weight);

        if (temp_lit[i] > 0)
          clause_lit_small[c][i].sense = 1;
        else
          clause_lit_small[c][i].sense = 0;

        var_lit_count[clause_lit_small[c][i].var_num]++;
      }

      clause_max_weight_small[c] = max_weight;

      avg_clause_coe_small[c] =
          round(double(avg_clause_coe_small[c] / (double)clause_lit_count[c]));
      if (avg_clause_coe_small[c] < 1)
        avg_clause_coe_small[c] = 1;

      clause_lit_small[c][i].var_num = 0;
      clause_lit_small[c][i].clause_num = -1;
      clause_lit_small[c][i].weight = 0;

      if (symbol == "=")
      {
        max_weight = 0; // find max_weight
        c = c_more;
        clause_lit_small[c] = new lit_small[clause_lit_count[c] + 1];

        for (i = 0; i < clause_lit_count[c]; ++i)
        {
          clause_lit_small[c][i].clause_num = c;
          clause_lit_small[c][i].var_num = abs(equal_temp_lit[i]);
          clause_lit_small[c][i].weight = equal_temp_weight[i];
          if (equal_temp_weight[i] > max_weight)
            max_weight = equal_temp_weight[i]; // max_weight
          avg_clause_coe_small[c] += double(clause_lit_small[c][i].weight);

          if (equal_temp_lit[i] > 0)
            clause_lit_small[c][i].sense = 1;
          else
            clause_lit_small[c][i].sense = 0;

          var_lit_count[clause_lit_small[c][i].var_num]++;
        }

        clause_max_weight_small[c] = max_weight;
        avg_clause_coe_small[c] =
            round(double(avg_clause_coe_small[c] / (double)clause_lit_count[c]));
        if (avg_clause_coe_small[c] < 1)
          avg_clause_coe_small[c] = 1;

        clause_lit_small[c][i].var_num = 0;
        clause_lit_small[c][i].clause_num = -1;
        clause_lit_small[c][i].weight = 0;
      }
    }
    // Handle var
    else if (s[0] == 'x')
    {
      temp_weight[clause_lit_count[c]] = coeff;
      temp_lit[clause_lit_count[c]] = stoi(s.substr(1));
      ++clause_lit_count[c];
    }
    else if (s == ";")
      ++c, clause_lit_count[c] = 0;
    // If comment or objective function push iterator past line
    else if (s == "*" || s[0] == '*' || s[0] == 'm')
      std::getline(file, commentLineTemp);
  }

  file.close();
  file.open(filename, std::ifstream::in);

  while (file >> s)
  {
    if (s == "*" || s[0] == '*')
      std::getline(file, commentLineTemp);
    else if (s == "min:")
      loadingObj = true;
    else if (s == ";")
    {
      loadingObj = false;
    }
    else if (loadingObj)
    {
      if (s[0] == '-' || s[0] == '+' || isdigit(s[0]))
        coeff = std::stoll(s);
      else
      {
        clause_lit_count[c] = 1;
        clause_lit_small[c] = new lit_small[clause_lit_count[c] + 1];
        if (coeff < 0)
        {
          clause_lit_small[c][0].var_num = std::stoi(s.substr(1));
          clause_lit_small[c][0].clause_num = c;
          clause_lit_small[c][0].weight = 1;
          clause_lit_small[c][0].sense = 1;
          org_clause_weight_small[c] = -coeff;
        }
        else
        {
          clause_lit_small[c][0].var_num = std::stoi(s.substr(1));
          clause_lit_small[c][0].clause_num = c;
          clause_lit_small[c][0].weight = 1;
          clause_lit_small[c][0].sense = 0;
          org_clause_weight_small[c] = coeff;
        }
        clause_max_weight_small[c] = 1;
        var_lit_count[clause_lit_small[c][0].var_num]++;
        clause_true_lit_thres_small[c] = 1;
        clause_lit_small[c][1].var_num = 0;
        clause_lit_small[c][1].clause_num = -1;
        clause_lit_small[c][1].weight = 0;
        c++;
      }
    }
    else
    {
      file.close();
      file.open(filename, std::ifstream::in);
      break;
    }
  }

  delete[] temp_weight; // zyj
  delete[] temp_lit;

  // creat var literal arrays
  for (v = 1; v <= num_vars; ++v)
  {
    var_lit_small[v] = new lit_small[var_lit_count[v] + 1];
    var_lit_count[v] = 0; // reset to 0, for build up the array
  }

  // scan all clauses to build up var literal arrays
  num_hclauses = num_sclauses = 0; // modify
  for (c = 0; c < num_clauses; ++c)
  {
    for (i = 0; i < clause_lit_count[c]; ++i)
    {
      v = clause_lit_small[c][i].var_num;
      var_lit_small[v][var_lit_count[v]] = clause_lit_small[c][i];
      ++var_lit_count[v];
    }
    clause_visied_times[c] = 0; // wyy

    if (org_clause_weight_small[c] != top_clause_weight_small)
    {
      total_soft_weight_small += org_clause_weight_small[c];
      // num_sclauses++; //privious-DeepOpt-v1
      soft_clause_num_index[num_sclauses++] = c; // NuPBO
    }
    else
    {
      hard_clause_num_index[num_hclauses++] = c; // NuPBO
    }
  }
  for (v = 1; v <= num_vars; ++v)
    var_lit_small[v][var_lit_count[v]].clause_num = -1;

  build_neighbor_relation_small();

  best_soln_feasible = 0;
  opt_unsat_weight_small = total_soft_weight_small + 1;
  opt_realobj_small = total_soft_weight_small + 1;
}

void Satlike::init_small(vector<int> &init_solution)
{
  int v, c;
  int j;
  float initsoftw = 0;

  local_times = 0; // MAB
  if_exceed = 0;
  if_exceed_hard = 0;
  hard_unsat_weight_small = 0; // zyj

  // local_soln_feasible = 0;
  // local_opt_unsat_weight = top_clause_weight_small + 1;
  //  large_weight_clauses_count = 0;
  //  soft_large_weight_clauses_count = 0;

  ave_soft_weight_small = num_sclauses == 0 ? 0 : total_soft_weight_small / num_sclauses;
  ave_hard_weight_small = 0;
  inc_hard_weight_small = 0;
  // cout << "ave soft weight is " << ave_soft_weight_small << endl;

  double tmp_avg_soft_clause_weight = 0.0; // Nupbo-zyj3.7

  tmp_avg_soft_clause_weight = num_sclauses == 0 ? 0 : round(double(top_clause_weight_small - 1) / num_sclauses);
  if (tmp_avg_soft_clause_weight < 1)
    tmp_avg_soft_clause_weight = 1;

  // Initialize clause information
  for (c = 0; c < num_clauses; c++)
  {
    selected_times[c] = 0;          // MAB-s
    clause_score_small[c] = 1;      // MAB-s
    selected_times_hard[c] = 0;     // MAB-hselectd_times_hard
    clause_hard_score_small[c] = 1; // MAB-h

    clause_visied_times[c] = 0;
    // clause_selected_count[c] = 0;

    if (org_clause_weight_small[c] == top_clause_weight_small)
    {
      // clause_weight_small[c] = clause_true_lit_thres_small[c];
      org_unit_weight_small[c] = 1;
      unit_weight_small[c] = org_unit_weight_small[c];
      tuned_degree_unit_weight_small[c] =
          double(unit_weight_small[c]) / avg_clause_coe_small[c]; // Nupbo-zyj3.7
      long long total_sum = 0;
      for (int i = 0; i < clause_lit_count[c]; ++i)
      {
        total_sum += clause_lit_small[c][i].weight;
      }
      clause_weight_small[c] = total_sum / clause_lit_count[c];
      ave_hard_weight_small += clause_weight_small[c];
      clause_total_sum_small[c] = total_sum; // 硬子句系数之和
    }
    else
    {
      tune_soft_clause_weight_small[c] = double(
          org_clause_weight_small[c] / tmp_avg_soft_clause_weight); // Nupbo-zyj3.7
      unit_weight_small[c] = initsoftw;                             // Nupbo-zyj3.7

      clause_weight_small[c] = org_clause_weight_small[c];
      clause_total_sum_small[c] = org_clause_weight_small[c]; // 软子句系数之和
      org_unit_weight_small[c] =
          ceil((double)clause_weight_small[c] / (double)clause_true_lit_thres_small[c]);
      // unit_weight_small[c] = org_unit_weight_small[c];
    }
    /********min{k + amax, asum}**********/
    if (clause_true_lit_thres_small[c] + clause_max_weight_small[c] <=
        clause_total_sum_small[c])
    {
      gap1_small[c] = clause_true_lit_thres_small[c] + clause_max_weight_small[c];
    }
    else
      gap1_small[c] = clause_total_sum_small[c];
    // gap1_small[c] = min((int)(clause_true_lit_thres_small[c] + clause_max_weight_small[c]),
    // (int)clause_total_sum_small[c]);//gap1_small 一样
    /********min{k + amax, asum}**********/
  }
  inc_hard_weight_small = ave_hard_weight_small % num_hclauses;
  ave_hard_weight_small /= num_hclauses;
  inc_hard_weight_small += ave_soft_weight_small;

  if (init_solution.size() == 0)
  {
    if (best_soln_feasible == 1)
    {
      for (v = 1; v <= num_vars; v++)
      {
        cur_soln[v] = best_soln[v];
        time_stamp[v] = 0;
        // cout << cur_soln[v] << endl;
        //  unsat_app_count[v] = 0;
      }
    }
    else
    {
      for (v = 1; v <= num_vars; v++)
      {
        cur_soln[v] = 0;
        time_stamp[v] = 0;
        // unsat_app_count[v] = 0;
      }
    }
  }
  else
  {
    for (v = 1; v <= num_vars; v++)
    {
      cur_soln[v] = init_solution[v];
      if (cur_soln[v] == 2)
        cur_soln[v] = rand() % 2;
      time_stamp[v] = 0;
      // unsat_app_count[v] = 0;
    }
  }

  // init_small stacks
  hard_unsat_nb = 0;
  hardunsat_stack_fill_pointer = 0;
  softunsat_stack_fill_pointer = 0;
  unsatvar_stack_fill_pointer = 0;
  /* figure out sat_count_small, sat_var, soft_unsat_weight_small and init_small unsat_stack */
  soft_unsat_weight_small = 0;

  for (c = 0; c < num_clauses; ++c)
  {
    sat_count_small[c] = 0;
    for (j = 0; j < clause_lit_count[c]; ++j)
    {
      if (cur_soln[clause_lit_small[c][j].var_num] == clause_lit_small[c][j].sense)
      {
        sat_count_small[c] += clause_lit_small[c][j].weight;
        // sat_var[c] = clause_lit_small[c][j].var_num;
      }
    }
    if (sat_count_small[c] < clause_true_lit_thres_small[c])
    {
      if (org_clause_weight_small[c] != top_clause_weight_small)
        soft_unsat_weight_small +=
            (clause_true_lit_thres_small[c] - sat_count_small[c]) * org_unit_weight_small[c];
      else
        hard_unsat_weight_small += clause_true_lit_thres_small[c] - sat_count_small[c]; // zyj
      unsat_small(c);
    }
    // cout<<"soft_unsat_weight_small "<<soft_unsat_weight_small<<endl;
  }

  /*figure out score_small*/
  int sense;
  long long weight;

  for (v = 1; v <= num_vars; v++)
  {
    score_small[v] = 0;
    sscore_small[v] = 0;
    hhscore_small[v] = 0; // 初始化hhscore
    for (int i = 0; i < var_lit_count[v]; ++i)
    {
      c = var_lit_small[v][i].clause_num;
      sense = var_lit_small[v][i].sense;
      weight = var_lit_small[v][i].weight;
      if (org_clause_weight_small[c] == top_clause_weight_small) // 加入了hhscore
      {
        if (sat_count_small[c] < clause_true_lit_thres_small[c])
        {
          if (sense != cur_soln[v]) // 当约束不满足时，可以直接加入hhscore
          {
            score_small[v] +=
                double(tuned_degree_unit_weight_small[c] *
                       min(clause_true_lit_thres_small[c] - sat_count_small[c], weight));
            // hhscore_small[v] += unit_weight_small[c] * max(weight -
            // (clause_true_lit_thres_small[c] - sat_count_small[c]), 0);
            hhscore_small[v] +=
                1 *
                max(weight - (clause_true_lit_thres_small[c] - sat_count_small[c]), 0LL);
          }
          else
          {
            score_small[v] -= double(tuned_degree_unit_weight_small[c] * weight);
            hhscore_small[v] += 0;
          }
        }
        else if (sat_count_small[c] >= clause_true_lit_thres_small[c])
        {
          if (sat_count_small[c] <= gap1_small[c])
          {
            if (sense == cur_soln[v])
            {
              score_small[v] -= double(
                  tuned_degree_unit_weight_small[c] *
                  max(0LL, clause_true_lit_thres_small[c] - sat_count_small[c] + weight));
              // hhscore_small[v] -= unit_weight_small[c] * min(weight, sat_count_small[c] -
              // clause_true_lit_thres_small[c]);
              hhscore_small[v] -=
                  1 * min(weight, sat_count_small[c] - clause_true_lit_thres_small[c]);
            }
            else
            {
              // hhscore_small[v] += unit_weight_small[c] * min(weight, gap1_small[c] -
              // sat_count_small[c]);
              hhscore_small[v] += 1 * min(weight, gap1_small[c] - sat_count_small[c]);
            }
          }
          else if (sat_count_small[c] > gap1_small[c])
          {
            if (sense == cur_soln[v])
            {
              score_small[v] -= double(
                  tuned_degree_unit_weight_small[c] *
                  max(0LL, clause_true_lit_thres_small[c] - sat_count_small[c] + weight));
              // hhscore_small[v] -= unit_weight_small[c] * max(weight - (sat_count_small[c] -
              // gap1_small[c]), 0);
              hhscore_small[v] -= 1 * max(weight - (sat_count_small[c] - gap1_small[c]), 0LL);
            }
          }
        }
      }
      else
      {
        if (sat_count_small[c] < clause_true_lit_thres_small[c])
        {
          if (sense != cur_soln[v])
          {
            sscore_small[v] += unit_weight_small[c] * tune_soft_clause_weight_small[c];
          }
          else
            sscore_small[v] -= unit_weight_small[c] * tune_soft_clause_weight_small[c];
        }
        else if (sat_count_small[c] >= clause_true_lit_thres_small[c])
        {
          if (sense == cur_soln[v])
          {
            sscore_small[v] -= unit_weight_small[c] * tune_soft_clause_weight_small[c];
          }
        }
      }
    }
  }

  // init_small goodvars stack
  goodvar_stack_fill_pointer = 0;

  for (v = 1; v <= num_vars; v++)
  {
    // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v] > 0)//加入hhscore
    if (score_small[v] + sscore_small[v] > 0)
    {
      already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
      mypush(v, goodvar_stack);
    }
    else
      already_in_goodvar_stack[v] = -1;
  }
}

int Satlike::pick_softc_small()
{
  int sel_c;

  sampled_clauses[0] = softunsat_stack[rand() % softunsat_stack_fill_pointer];
  double min = clause_score_small[sampled_clauses[0]],
         max = clause_score_small[sampled_clauses[0]];

  for (int i = 1; i < ArmNum; i++) // 20sample min max ???
  {
    sampled_clauses[i] = softunsat_stack[rand() % softunsat_stack_fill_pointer];

    if (clause_score_small[sampled_clauses[i]] < min)
      min = clause_score_small[sampled_clauses[i]];
    if (clause_score_small[sampled_clauses[i]] > max)
      max = clause_score_small[sampled_clauses[i]];
  }
  if (max == min) // time比较
  {
    sel_c = sampled_clauses[0];
    for (int i = 1; i < ArmNum; i++)
    {
      if (selected_times[sampled_clauses[i]] < selected_times[sel_c])
        sel_c = sampled_clauses[i];
      else if (selected_times[sampled_clauses[i]] == selected_times[sel_c])
      {
        if (clause_weight_small[sampled_clauses[i]] > clause_weight_small[sel_c])
          sel_c = sampled_clauses[i];
      }
    }
  }
  else
  {
    double max_value =
        clause_score_small[sampled_clauses[0]] +
        lambda * sqrt((log(local_times + 1)) /
                      ((double)(selected_times[sampled_clauses[0]] + 1)));
    sel_c = sampled_clauses[0];
    for (int i = 1; i < ArmNum; i++) // 20个最大的lambda
    {
      double dtemp =
          clause_score_small[sampled_clauses[i]] +
          lambda * sqrt((log(local_times + 1)) /
                        ((double)(selected_times[sampled_clauses[i]] + 1)));
      if (dtemp > max_value)
      {
        max_value = dtemp;
        sel_c = sampled_clauses[i];
      }
    }
  }
  selected_times[sel_c]++;
  selected_clauses[local_times % backward_step] = sel_c; // ？？？
  if (local_times > 0)
  {
    long long s = pre_unsat_weight_small - soft_unsat_weight_small;
    update_clause_scores_small(s);
  }
  pre_unsat_weight_small = soft_unsat_weight_small;
  local_times++;

  return sel_c;
}

void Satlike::update_clause_scores_small(long long s)
{
  int i, j;
  double stemp;

  long long opt = opt_unsat_weight_small;
  if (soft_unsat_weight_small < opt)
    opt = soft_unsat_weight_small;

  stemp = ((double)s) / (pre_unsat_weight_small - opt + 1); // reward

  double discount;
  if (local_times < backward_step)
  {
    for (i = 0; i < local_times; i++)
    {
      discount = pow(gamma, local_times - 1 - i);
      clause_score_small[selected_clauses[i]] += (discount * ((double)stemp));
      if (abs(clause_score_small[selected_clauses[i]]) > max_clause_score_small)
        if_exceed = 1;
    }
  }
  else
  {
    for (i = 0; i < backward_step; i++)
    {
      if (i == local_times % backward_step)
        continue;
      if (i < local_times % backward_step)
        discount = pow(gamma, local_times % backward_step - 1 - i);
      else
        discount =
            pow(gamma, local_times % backward_step + backward_step - 1 - i);
      clause_score_small[selected_clauses[i]] += (discount * ((double)stemp));
      if (abs(clause_score_small[selected_clauses[i]]) > max_clause_score_small)
        if_exceed = 1;
    }
  }
  if (if_exceed)
  {
    for (i = 0; i < num_clauses; i++)
      clause_score_small[i] = clause_score_small[i] / 2.0;
    if_exceed = 0;
  }
}

int Satlike::pick_hardc_small()
{
  int sel_c;

  sampled_clauses_hard[0] =
      hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
  double min = clause_hard_score_small[sampled_clauses_hard[0]],
         max = clause_hard_score_small[sampled_clauses_hard[0]];

  for (int i = 1; i < ArmNum; i++) // 20sample min max ???
  {
    sampled_clauses_hard[i] =
        hardunsat_stack[rand() % hardunsat_stack_fill_pointer];

    if (clause_hard_score_small[sampled_clauses_hard[i]] < min)
      min = clause_hard_score_small[sampled_clauses_hard[i]];
    if (clause_hard_score_small[sampled_clauses_hard[i]] > max)
      max = clause_hard_score_small[sampled_clauses_hard[i]];
  }
  if (max == min) // time比较
  {
    sel_c = sampled_clauses_hard[0];
    for (int i = 1; i < ArmNum; i++)
    {
      if (selected_times_hard[sampled_clauses_hard[i]] <
          selected_times_hard[sel_c])
        sel_c = sampled_clauses_hard[i];
      else if (selected_times_hard[sampled_clauses_hard[i]] ==
               selected_times_hard[sel_c])
      {
        // if (clause_weight_small[sampled_clauses[i]] > clause_weight_small[sel_c])
        if (rand() % 100 < 50)
          sel_c = sampled_clauses_hard[i];
      }
    }
  }
  else
  {
    double max_value =
        clause_hard_score_small[sampled_clauses_hard[0]] +
        lambda *
            sqrt((log(local_times_hard + 1)) /
                 ((double)(selected_times_hard[sampled_clauses_hard[0]] + 1)));
    sel_c = sampled_clauses_hard[0];
    for (int i = 1; i < ArmNum; i++) // 20个最大的lambda
    {
      double dtemp =
          clause_hard_score_small[sampled_clauses_hard[i]] +
          lambda * sqrt((log(local_times_hard + 1)) /
                        ((double)(selected_times_hard[sampled_clauses_hard[i]] +
                                  1)));
      if (dtemp > max_value)
      {
        max_value = dtemp;
        sel_c = sampled_clauses_hard[i];
      }
    }
  }
  selected_times_hard[sel_c]++;
  selected_clauses_hard[local_times_hard % backward_step] = sel_c; // ？？？
  if (local_times_hard > 0)
  {
    // long long s = pre_unsat_weight_small - soft_unsat_weight_small;
    // long long s = pre_unsat_hard_nb - hard_unsat_nb;
    long long s = pre_hard_unsat_weight_small - hard_unsat_weight_small; // zyj
    update_clause_scores_hard_small(s);
  }
  // pre_unsat_weight_small = soft_unsat_weight_small;
  // pre_unsat_hard_nb = hard_unsat_nb;
  pre_hard_unsat_weight_small = hard_unsat_weight_small; // zyj
  local_times_hard++;

  return sel_c;
}

void Satlike::update_clause_scores_hard_small(long long s)
{
  int i, j;
  double stemp;

  // stemp = ((double)s) / (pre_unsat_hard_nb + 1); // reward
  stemp = ((double)s) / (pre_hard_unsat_weight_small + 1); // zyj

  double discount;
  if (local_times_hard < backward_step)
  {
    for (i = 0; i < local_times_hard; i++)
    {
      discount = pow(gamma, local_times_hard - 1 - i);
      clause_hard_score_small[selected_clauses_hard[i]] +=
          (discount * ((double)stemp));
      if (abs(clause_hard_score_small[selected_clauses_hard[i]]) > 1000)
        if_exceed_hard = 1;
    }
  }
  else
  {
    for (i = 0; i < backward_step; i++)
    {
      if (i == local_times_hard % backward_step)
        continue;
      if (i < local_times_hard % backward_step)
        discount = pow(gamma, local_times_hard % backward_step - 1 - i);
      else
        discount = pow(gamma, local_times_hard % backward_step + backward_step -
                                  1 - i);
      clause_hard_score_small[selected_clauses_hard[i]] +=
          (discount * ((double)stemp));
      if (abs(clause_hard_score_small[selected_clauses_hard[i]]) > 1000)
        if_exceed_hard = 1;
    }
  }
  if (if_exceed_hard)
  {
    for (i = 0; i < num_clauses; i++)
      clause_hard_score_small[i] = clause_hard_score_small[i] / 2.0;
    if_exceed_hard = 0;
  }
}

void Satlike::pick_vars_small() // new adds
{
  int i, v, j;
  int best_var;
  int rand_select; // 使用hhscore，随机选择
  int mark_v1 = 0;
  int mark_v2 = 0;
  // int better_var1;

  update_clause_weights_small();
  int sel_c;
  int sel_c_set[100];
  lit_small *p;
  int mark_which = 0;
  if (hardunsat_stack_fill_pointer > 0)
  {
    // if (step < 10000 || best_soln_feasible > 0) // MAB-h
    // if (best_soln_feasible > 0) // MAB-h
    //{
    if (hardunsat_stack_fill_pointer < 100)
    {
      sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
      mark_which = 1;
    }
    else
    {
      sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
      for (i = 0; i < 100; i++)
      {
        sel_c_set[i] = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
      }
      mark_which = 2;
    }
  }
  else
  {
    // sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
    sel_c = pick_softc_small();
    mark_which = 3;
  }

  if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
  {
    best_var = clause_lit_small[sel_c][rand() % clause_lit_count[sel_c]].var_num;
    flip_small(best_var);
    return;
  }
  // return clause_lit_small[sel_c][rand() % clause_lit_count[sel_c]].var_num;

  if (clause_lit_count[sel_c] == 1)
  {
    best_var = clause_lit_small[sel_c][0].var_num;
    flip_small(best_var);
    return;
  }
  else if (clause_lit_count[sel_c] == 2)
  {
    int v1 = clause_lit_small[sel_c][0].var_num;
    int v2 = clause_lit_small[sel_c][1].var_num;
    if (rand() % 100 < 0)
    {
      if (rand() % 100 < 50)
        best_var = v1;
      else
        best_var = v2;
    }
    else
    {
      score_baocun_small[0] = score_small[v1]; // baocun score_small
      sscore_baocun_small[0] = sscore_small[v1];
      hhscore_baocun_small[0] = hhscore_small[v1];
      score_baocun_small[1] = score_small[v2];
      sscore_baocun_small[1] = sscore_small[v2];
      hhscore_baocun_small[1] = hhscore_small[v2];
      for (i = 0; i < num_vars; i++)
      {
        goodvar_stack2[i] = 0;
      }

      int best_v1_neighbor;
      int best_v2_neighbor;
      flip_fps_small(v1);
      if (goodvar_stack2_num > 0)
      {
        mark_v1 = 1;
        if (goodvar_stack2_num < 15)
        {
          best_v1_neighbor = goodvar_stack2[0];
          for (j = 1; j < goodvar_stack2_num;
               ++j) // goodvar_stack2_num < sv_num, 取下界goodvar_stack2_num
          {
            v = goodvar_stack2[j];
            if (score2_small[v] + sscore2_small[v] >
                score2_small[best_v1_neighbor] +
                    sscore2_small[best_v1_neighbor]) /*New Added*/
              best_v1_neighbor = v;
            else if (score2_small[v] + sscore2_small[v] ==
                     score2_small[best_v1_neighbor] +
                         sscore2_small[best_v1_neighbor]) /*New Added*/
            {
              // if (time_stamp[v] < time_stamp[vars2[i]])//hhscore_small
              // best_v1_neighbor = v;
              if (hhscore2_small[v] > hhscore2_small[best_v1_neighbor])
              {
                best_v1_neighbor = v;
              }
              else if (hhscore2_small[v] == hhscore2_small[best_v1_neighbor])
              {
                rand_select = rand() % 2;
                if (rand_select == 1)
                {
                  best_v1_neighbor = v;
                }
              }
            }
          }
        }
        else
        {
          best_v1_neighbor = goodvar_stack2[rand() % goodvar_stack2_num];
          for (j = 1; j < 15; ++j) // goodvar_stack2_num >= sv_num, 取下界sv_num
          {
            v = goodvar_stack2[rand() % goodvar_stack2_num];
            if (score2_small[v] + sscore2_small[v] >
                score2_small[best_v1_neighbor] +
                    sscore2_small[best_v1_neighbor]) /*New Added*/
              best_v1_neighbor = v;
            else if (score2_small[v] + sscore2_small[v] ==
                     score2_small[best_v1_neighbor] +
                         sscore2_small[best_v1_neighbor]) /*New Added*/
            {
              if (hhscore2_small[v] > hhscore2_small[best_v1_neighbor])
              {
                best_v1_neighbor = v;
              }
              else if (hhscore2_small[v] == hhscore2_small[best_v1_neighbor])
              {
                rand_select = rand() % 2;
                if (rand_select == 1)
                {
                  best_v1_neighbor = v;
                }
              }
            }
          }
        }
        score_baocun_small[0] += score2_small[best_v1_neighbor];
        sscore_baocun_small[0] += sscore2_small[best_v1_neighbor]; /*New Added*/
        hhscore_baocun_small[0] += hhscore2_small[best_v1_neighbor];
      }
      else
      {
        mark_v1 = 0;
      }

      for (i = 0; i < num_vars; i++)
      {
        goodvar_stack2[i] = 0;
      }

      flip_fps_small(v2);
      if (goodvar_stack2_num > 0)
      {
        mark_v2 = 1;
        if (goodvar_stack2_num < 15)
        {
          best_v2_neighbor = goodvar_stack2[0];
          for (j = 1; j < goodvar_stack2_num;
               ++j) // goodvar_stack2_num < sv_num, 取下界goodvar_stack2_num
          {
            v = goodvar_stack2[j];
            if (score2_small[v] + sscore2_small[v] >
                score2_small[best_v2_neighbor] +
                    sscore2_small[best_v2_neighbor]) /*New Added*/
              best_v2_neighbor = v;
            else if (score2_small[v] + sscore2_small[v] ==
                     score2_small[best_v2_neighbor] +
                         sscore2_small[best_v2_neighbor]) /*New Added*/
            {
              if (hhscore2_small[v] > hhscore2_small[best_v2_neighbor])
              {
                best_v2_neighbor = v;
              }
              else if (hhscore2_small[v] == hhscore2_small[best_v2_neighbor])
              {
                rand_select = rand() % 2;
                if (rand_select == 1)
                {
                  best_v2_neighbor = v;
                }
              }
            }
          }
        }
        else
        {
          best_v2_neighbor = goodvar_stack2[rand() % goodvar_stack2_num];
          for (j = 1; j < 15; ++j) // goodvar_stack2_num >= sv_num, 取下界sv_num
          {
            v = goodvar_stack2[rand() % goodvar_stack2_num];
            if (score2_small[v] + sscore2_small[v] >
                score2_small[best_v2_neighbor] +
                    sscore2_small[best_v2_neighbor]) /*New Added*/
              best_v2_neighbor = v;
            else if (score2_small[v] + sscore2_small[v] ==
                     score2_small[best_v2_neighbor] +
                         sscore2_small[best_v2_neighbor]) /*New Added*/
            {
              if (hhscore2_small[v] > hhscore2_small[best_v2_neighbor])
              {
                best_v2_neighbor = v;
              }
              else if (hhscore2_small[v] == hhscore2_small[best_v2_neighbor])
              {
                rand_select = rand() % 2;
                if (rand_select == 1)
                {
                  best_v2_neighbor = v;
                }
              }
            }
          }
        }
        score_baocun_small[1] += score2_small[best_v2_neighbor];
        sscore_baocun_small[1] += sscore2_small[best_v2_neighbor]; /*New Added*/
        hhscore_baocun_small[1] += hhscore2_small[best_v2_neighbor];
      }
      else
      {
        mark_v2 = 0;
      }
      // int best_flip_neighbor;
      // int best_flip;
      if (mark_v1 == 1 && mark_v2 == 1)
      {
        if (score_baocun_small[0] + sscore_baocun_small[0] > 0 &&
            score_baocun_small[1] + sscore_baocun_small[1] > 0)
        {
          if (score_baocun_small[0] + sscore_baocun_small[0] >
              score_baocun_small[1] + sscore_baocun_small[1])
          {
            best_flip_neighbor = best_v1_neighbor;
            best_var = v1;
          }
          else if (score_baocun_small[0] + sscore_baocun_small[0] <
                   score_baocun_small[1] + sscore_baocun_small[1])
          {
            best_flip_neighbor = best_v2_neighbor;
            best_var = v2;
          }
          else
          {
            if (hhscore_baocun_small[0] > hhscore_baocun_small[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
            }
            else if (hhscore_baocun_small[0] < hhscore_baocun_small[1])
            {
              best_flip_neighbor = best_v2_neighbor;
              best_var = v2;
            }
            else
            {
              rand_select = rand() % 2;
              if (rand_select == 1)
              {
                best_var = v1;
                best_flip_neighbor = best_v1_neighbor;
              }
              else
              {
                best_var = v2;
                best_flip_neighbor = best_v2_neighbor;
              }
            }
          }
          flip_small(best_var);
          flip_small(best_flip_neighbor);
          return;
        }
        else if (score_baocun_small[0] + sscore_baocun_small[0] > 0 &&
                 score_baocun_small[1] + sscore_baocun_small[1] < 0)
        {
          best_flip_neighbor = best_v1_neighbor;
          best_var = v1;
          flip_small(best_var);
          flip_small(best_flip_neighbor);
          return;
        }
        else if (score_baocun_small[0] + sscore_baocun_small[0] < 0 &&
                 score_baocun_small[1] + sscore_baocun_small[1] > 0)
        {
          best_flip_neighbor = best_v2_neighbor;
          best_var = v2;
          flip_small(best_var);
          flip_small(best_flip_neighbor);
          return;
        }
        else // new addflip
        {
          if (score_small[v1] + sscore_small[v1] < score_baocun_small[0] + sscore_baocun_small[0] &&
              score_small[v2] + sscore_small[v2] < score_baocun_small[1] + sscore_baocun_small[1])
          {
            if (score_baocun_small[0] + sscore_baocun_small[0] >
                score_baocun_small[1] + sscore_baocun_small[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
            else if (score_baocun_small[0] + sscore_baocun_small[0] <
                     score_baocun_small[1] + sscore_baocun_small[1])
            {
              best_flip_neighbor = best_v2_neighbor;
              best_var = v2;
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
            else // 可以用hhscore or rand or teacher
            {
              if (hhscore_baocun_small[0] > hhscore_baocun_small[1])
              {
                best_flip_neighbor = best_v1_neighbor;
                best_var = v1;
              }
              else if (hhscore_baocun_small[0] < hhscore_baocun_small[1])
              {
                best_flip_neighbor = best_v2_neighbor;
                best_var = v2;
              }
              else
              {
                rand_select = rand() % 2;
                if (rand_select == 1)
                {
                  best_var = v1;
                  best_flip_neighbor = best_v1_neighbor;
                }
                else
                {
                  best_var = v2;
                  best_flip_neighbor = best_v2_neighbor;
                }
              }
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
          }
          else
          {
            if (score_small[v1] + sscore_small[v1] > score_small[v2] + sscore_small[v2])
            {
              best_var = v1;
            }
            else if (score_small[v1] + sscore_small[v1] < score_small[v2] + sscore_small[v2])
            {
              best_var = v2;
            }
            else
            {
              if (hhscore_small[v1] > hhscore_small[v2])
              {
                best_var = v1;
              }
              else if (hhscore_small[v1] < hhscore_small[v2])
              {
                best_var = v2;
              }
              else
              {
                if (rand() % 100 < 50)
                  best_var = v1;
                else
                  best_var = v2;
              }
            }
            flip_small(best_var);
            return;
          }
          // if(score_small[v1] + sscore_small[v1] > score_small[v2] + sscore_small[v2])
          // {
          // 	best_var = v1;
          // }
          // else if(score_small[v1] + sscore_small[v1] < score_small[v2] + sscore_small[v2])
          // {
          // 	best_var = v2;
          // }
          // else
          // {
          // 	if(hhscore_small[v1] > hhscore_small[v2])
          // 	{
          // 		best_var = v1;
          // 	}
          // 	else if(hhscore_small[v1] < hhscore_small[v2])
          // 	{
          // 		best_var = v2;
          // 	}
          // 	else
          // 	{
          // 		int rand_select = rand() % 2;
          // 		if(rand_select == 1)
          // 		{
          // 			best_var = v1;
          // 		}else
          // 		{
          // 			best_var = v2;
          // 		}
          // 	}
          // }
          // flip_small(best_var);
          // return;
        }

        //  if (scores[i] + sscores[i] > 0)
        //  {    /*New Added*/
        //  	flip_small(best_vars[i]);
        //  	flip_small(vars2[i]);
        //  	time_stamp[best_vars[i]] = step;
        //  	time_stamp[vars2[i]] = step;
        //  	return;
      }
      else if (mark_v1 == 1 && mark_v2 == 0)
      {
        if (score_baocun_small[0] + sscore_baocun_small[0] > 0)
        {
          best_var = v1;
          best_flip_neighbor = best_v1_neighbor;
          flip_small(best_var);
          flip_small(best_flip_neighbor);
          return;
        }
        else // new addflip
        {
          if (score_small[v1] + sscore_small[v1] < score_baocun_small[0] + sscore_baocun_small[0] &&
              score_small[v2] + sscore_small[v2] < score_baocun_small[1] + sscore_baocun_small[1])
          {
            if (score_baocun_small[0] + sscore_baocun_small[0] >
                score_baocun_small[1] + sscore_baocun_small[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
            else if (score_baocun_small[0] + sscore_baocun_small[0] <
                     score_baocun_small[1] + sscore_baocun_small[1])
            {
              best_flip_neighbor = best_v2_neighbor;
              best_var = v2;
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
            else
            {
              if (hhscore_baocun_small[0] > hhscore_baocun_small[1])
              {
                best_flip_neighbor = best_v1_neighbor;
                best_var = v1;
              }
              else if (hhscore_baocun_small[0] < hhscore_baocun_small[1])
              {
                best_flip_neighbor = best_v2_neighbor;
                best_var = v2;
              }
              else
              {
                rand_select = rand() % 2;
                if (rand_select == 1)
                {
                  best_var = v1;
                  best_flip_neighbor = best_v1_neighbor;
                }
                else
                {
                  best_var = v2;
                  best_flip_neighbor = best_v2_neighbor;
                }
              }
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
          }
          else
          {
            if (score_small[v1] + sscore_small[v1] > score_small[v2] + sscore_small[v2])
            {
              best_var = v1;
            }
            else if (score_small[v1] + sscore_small[v1] < score_small[v2] + sscore_small[v2])
            {
              best_var = v2;
            }
            else
            {
              if (hhscore_small[v1] > hhscore_small[v2])
              {
                best_var = v1;
              }
              else if (hhscore_small[v1] < hhscore_small[v2])
              {
                best_var = v2;
              }
              else
              {
                if (rand() % 100 < 50)
                  best_var = v1;
                else
                  best_var = v2;
              }
            }
            flip_small(best_var);
            return;
          }
          // if(score_small[v1] + sscore_small[v1] > score_small[v2] + sscore_small[v2])
          // {
          // 	best_var = v1;
          // }
          // else if(score_small[v1] + sscore_small[v1] < score_small[v2] + sscore_small[v2])
          // {
          // 	best_var = v2;
          // }
          // else
          // {
          // 	if(hhscore_small[v1] > hhscore_small[v2])
          // 	{
          // 		best_var = v1;
          // 	}
          // 	else if(hhscore_small[v1] < hhscore_small[v2])
          // 	{
          // 		best_var = v2;
          // 	}
          // 	else
          // 	{
          // 		int rand_select = rand() % 2;
          // 		if(rand_select == 1)
          // 		{
          // 			best_var = v1;
          // 		}else
          // 		{
          // 			best_var = v2;
          // 		}
          // 	}
          // }
          // flip_small(best_var);
          // return;
        }
      }
      else if (mark_v1 == 0 && mark_v2 == 1)
      {
        if (score_baocun_small[1] + sscore_baocun_small[1] > 0)
        {
          best_var = v2;
          best_flip_neighbor = best_v2_neighbor;
          flip_small(best_var);
          flip_small(best_flip_neighbor);
          return;
        }
        else // new addflip
        {
          if (score_small[v1] + sscore_small[v1] < score_baocun_small[0] + sscore_baocun_small[0] &&
              score_small[v2] + sscore_small[v2] < score_baocun_small[1] + sscore_baocun_small[1])
          {
            if (score_baocun_small[0] + sscore_baocun_small[0] >
                score_baocun_small[1] + sscore_baocun_small[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
            else if (score_baocun_small[0] + sscore_baocun_small[0] <
                     score_baocun_small[1] + sscore_baocun_small[1])
            {
              best_flip_neighbor = best_v2_neighbor;
              best_var = v2;
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
            else
            {
              if (hhscore_baocun_small[0] > hhscore_baocun_small[1])
              {
                best_flip_neighbor = best_v1_neighbor;
                best_var = v1;
              }
              else if (hhscore_baocun_small[0] < hhscore_baocun_small[1])
              {
                best_flip_neighbor = best_v2_neighbor;
                best_var = v2;
              }
              else
              {
                rand_select = rand() % 2;
                if (rand_select == 1)
                {
                  best_var = v1;
                  best_flip_neighbor = best_v1_neighbor;
                }
                else
                {
                  best_var = v2;
                  best_flip_neighbor = best_v2_neighbor;
                }
              }
              flip_small(best_var);
              flip_small(best_flip_neighbor);
              return;
            }
          }
          else
          {
            if (score_small[v1] + sscore_small[v1] > score_small[v2] + sscore_small[v2])
            {
              best_var = v1;
            }
            else if (score_small[v1] + sscore_small[v1] < score_small[v2] + sscore_small[v2])
            {
              best_var = v2;
            }
            else
            {
              if (hhscore_small[v1] > hhscore_small[v2])
              {
                best_var = v1;
              }
              else if (hhscore_small[v1] < hhscore_small[v2])
              {
                best_var = v2;
              }
              else
              {
                if (rand() % 100 < 50)
                  best_var = v1;
                else
                  best_var = v2;
              }
            }
            flip_small(best_var);
            return;
          }
          // if(score_small[v1] + sscore_small[v1] > score_small[v2] + sscore_small[v2])
          // {
          // 	best_var = v1;
          // }
          // else if(score_small[v1] + sscore_small[v1] < score_small[v2] + sscore_small[v2])
          // {
          // 	best_var = v2;
          // }
          // else
          // {
          // 	if(hhscore_small[v1] > hhscore_small[v2])
          // 	{
          // 		best_var = v1;
          // 	}
          // 	else if(hhscore_small[v1] < hhscore_small[v2])
          // 	{
          // 		best_var = v2;
          // 	}
          // 	else
          // 	{
          // 		int rand_select = rand() % 2;
          // 		if(rand_select == 1)
          // 		{
          // 			best_var = v1;
          // 		}else
          // 		{
          // 			best_var = v2;
          // 		}
          // 	}
          // }
          // flip_small(best_var);
          // return;
        }
      }
      else // new added
      {
        if (score_small[v1] + sscore_small[v1] < score_baocun_small[0] + sscore_baocun_small[0] &&
            score_small[v2] + sscore_small[v2] < score_baocun_small[1] + sscore_baocun_small[1])
        {
          if (score_baocun_small[0] + sscore_baocun_small[0] >
              score_baocun_small[1] + sscore_baocun_small[1])
          {
            best_flip_neighbor = best_v1_neighbor;
            best_var = v1;
            flip_small(best_var);
            flip_small(best_flip_neighbor);
            return;
          }
          else if (score_baocun_small[0] + sscore_baocun_small[0] <
                   score_baocun_small[1] + sscore_baocun_small[1])
          {
            best_flip_neighbor = best_v2_neighbor;
            best_var = v2;
            flip_small(best_var);
            flip_small(best_flip_neighbor);
            return;
          }
          else
          {
            if (hhscore_baocun_small[0] > hhscore_baocun_small[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
            }
            else if (hhscore_baocun_small[0] < hhscore_baocun_small[1])
            {
              best_flip_neighbor = best_v2_neighbor;
              best_var = v2;
            }
            else
            {
              rand_select = rand() % 2;
              if (rand_select == 1)
              {
                best_var = v1;
                best_flip_neighbor = best_v1_neighbor;
              }
              else
              {
                best_var = v2;
                best_flip_neighbor = best_v2_neighbor;
              }
            }
            flip_small(best_var);
            flip_small(best_flip_neighbor);
            return;
          }
        }
        else
        {
          if (score_small[v1] + sscore_small[v1] > score_small[v2] + sscore_small[v2])
          {
            best_var = v1;
          }
          else if (score_small[v1] + sscore_small[v1] < score_small[v2] + sscore_small[v2])
          {
            best_var = v2;
          }
          else
          {
            if (hhscore_small[v1] > hhscore_small[v2])
            {
              best_var = v1;
            }
            else if (hhscore_small[v1] < hhscore_small[v2])
            {
              best_var = v2;
            }
            else
            {
              if (rand() % 100 < 50)
                best_var = v1;
              else
                best_var = v2;
            }
          }
          flip_small(best_var);
          return;
        }
      }
    }
  }
  else
  {
    /********BMS********/
    // if() {printf("wrong else\n");
    if (mark_which == 1 || mark_which == 3)
    {
      int bms;
      if (clause_lit_count[sel_c] <= 200)
      {
        bms = (clause_lit_count[sel_c] - 1) / 2 +
              1; // 选择子句的变量个数除2，向上取整
      }
      else
      {
        bms = 100;
      }

      best_var = clause_lit_small[sel_c][rand() % clause_lit_count[sel_c]].var_num;
      for (i = 1; i < bms; i++)
      {
        v = clause_lit_small[sel_c][rand() % clause_lit_count[sel_c]].var_num;
        if (score_small[v] + sscore_small[v] > score_small[best_var] + sscore_small[best_var])
          best_var = v;
        else if (score_small[v] + sscore_small[v] == score_small[best_var] + sscore_small[best_var])
        {
          if (hhscore_small[v] > hhscore_small[best_var])
          {
            best_var = v;
          }
          else if (hhscore_small[v] == hhscore_small[best_var])
          {
            rand_select = rand() % 2;
            if (rand_select == 1)
            {
              best_var = v;
            }
          }
        }
      }
    }
    else
    {
      best_var =
          clause_lit_small[sel_c_set[0]][rand() % clause_lit_count[sel_c_set[0]]]
              .var_num;
      for (j = 0; j < 100; j++)
      {
        // int bms = (clause_lit_count[sel_c_set[j]] - 1) / 2 + 1;
        // //选择子句的变量个数除2，向上取整 best_var = clause_lit_small[sel_c][rand()
        // % clause_lit_count[sel_c]].var_num;
        int bms;
        if (clause_lit_count[sel_c] <= 200)
        {
          bms = (clause_lit_count[sel_c] - 1) / 2 +
                1; // 选择子句的变量个数除2，向上取整
        }
        else
        {
          bms = 100;
        }
        for (i = 0; i < bms; i++)
        {
          v = clause_lit_small[sel_c_set[j]][rand() % clause_lit_count[sel_c_set[j]]]
                  .var_num;
          if (score_small[v] + sscore_small[v] > score_small[best_var] + sscore_small[best_var])
            best_var = v;
          else if (score_small[v] + sscore_small[v] == score_small[best_var] + sscore_small[best_var])
          {
            if (hhscore_small[v] > hhscore_small[best_var])
            {
              best_var = v;
            }
            else if (hhscore_small[v] == hhscore_small[best_var])
            {
              rand_select = rand() % 2;
              if (rand_select == 1)
              {
                best_var = v;
              }
            }
          }
        }
      }
    }
    flip_small(best_var);
    return;
  }
  /********BMS********/
  // flip_small(best_var);
  // return;
}

int Satlike::pick_var_small() // new adds
{
  int i, v, j;
  int best_var;
  int rand_select; // 使用hhscore，随机选择

  if (goodvar_stack_fill_pointer > 0)
  {
    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
    {
      return goodvar_stack[rand() % goodvar_stack_fill_pointer];
    }

    if (goodvar_stack_fill_pointer < hd_count_threshold) // 15
    {
      best_var = goodvar_stack[0];
      for (i = 1; i < goodvar_stack_fill_pointer; ++i)
      {
        v = goodvar_stack[i];
        if (score_small[v] + sscore_small[v] > score_small[best_var] + sscore_small[best_var])
          best_var = v;
        else if (score_small[v] + sscore_small[v] == score_small[best_var] + sscore_small[best_var])
        {
          if (hhscore_small[v] > hhscore_small[best_var])
          {
            best_var = v;
          }
          else if (hhscore_small[v] == hhscore_small[best_var])
          {
            rand_select = rand() % 2;
            if (rand_select == 1)
            {
              best_var = v;
            }
          }
        }
      }
      return best_var;
    }
    else
    {
      int r = rand() % goodvar_stack_fill_pointer;
      best_var = goodvar_stack[r];

      for (i = 1; i < hd_count_threshold; ++i)
      {
        r = rand() % goodvar_stack_fill_pointer;
        v = goodvar_stack[r];
        if (score_small[v] + sscore_small[v] > score_small[best_var] + sscore_small[best_var])
          best_var = v;
        else if (score_small[v] + sscore_small[v] == score_small[best_var] + sscore_small[best_var])
        {
          if (hhscore_small[v] > hhscore_small[best_var])
          {
            best_var = v;
          }
          else if (hhscore_small[v] == hhscore_small[best_var])
          {
            rand_select = rand() % 2;
            if (rand_select == 1)
            {
              best_var = v;
            }
          }
        }
      }
      return best_var;
    }
  }

  update_clause_weights_small();

  int sel_c;
  int sel_c_set[100];
  lit_small *p;
  int mark_which = 0;

  if (hardunsat_stack_fill_pointer > 0)
  {
    if (hardunsat_stack_fill_pointer < 100)
    {
      sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
      mark_which = 1;
    }
    else
    {
      sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
      for (i = 0; i < 100; i++)
      {
        sel_c_set[i] = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
      }
      mark_which = 2;
    }
  }
  else
  {
    // sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
    sel_c = pick_softc_small(); // MAB
    mark_which = 3;
  }
  if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
    return clause_lit_small[sel_c][rand() % clause_lit_count[sel_c]].var_num;

  if (clause_lit_count[sel_c] == 1)
  {
    best_var = clause_lit_small[sel_c][0].var_num;
  }
  else if (clause_lit_count[sel_c] == 2)
  {
    int v1 = clause_lit_small[sel_c][0].var_num;
    int v2 = clause_lit_small[sel_c][1].var_num;
    if (rand() % 100 < 0)
    {
      if (rand() % 100 < 50)
        best_var = v1;
      else
        best_var = v2;
    }
    else
    {

      if (score_small[v1] + sscore_small[v1] > score_small[v2] + sscore_small[v2])
      {
        best_var = v1;
      }
      else if (score_small[v1] + sscore_small[v1] < score_small[v2] + sscore_small[v2])
      {
        best_var = v2;
      }
      else
      {
        if (hhscore_small[v1] > hhscore_small[v2])
        {
          best_var = v1;
        }
        else if (hhscore_small[v1] < hhscore_small[v2])
        {
          best_var = v2;
        }
        else
        {
          int rand_select = rand() % 2;
          if (rand_select == 1)
          {
            best_var = v1;
          }
          else
          {
            best_var = v2;
          }
        }
      }
    }
  }
  /*
          else if(clause_lit_count[sel_c] == 2){
                  int v1 = clause_lit_small[sel_c][0].var_num;
                  int v2 = clause_lit_small[sel_c][1].var_num;

                  //if(time_stamp[v1] + 55  > step)
                  //	best_var = v2;
                  //else if(time_stamp[v2] + 5  > step)
                  //	best_var = v1;
                  //else
                  if(score_small[v1] + sscore_small[v1] == score_small[v2] + sscore_small[v2])
                          best_var = clause_lit_small[sel_c][rand() % 2].var_num;
                  else if(score_small[v1] + sscore_small[v1] < 0 && score_small[v2] + sscore_small[v2]
     >= 0) best_var = v2; else if(score_small[v2] + sscore_small[v2] < 0 && score_small[v1] +
     sscore_small[v1] >= 0) best_var = v1; else if(score_small[v1] + sscore_small[v1] < 0 &&
     score_small[v2] + sscore_small[v2] < 0){ int tt = -1 * (score_small[v1] + sscore_small[v1] +
     score_small[v2] + sscore_small[v2]); int rand_num = rand() % tt; if(rand_num < -1 *
     score_small[v1] - sscore_small[v1]) best_var = v2; else best_var = v1;
                  }
                  else{
                          int tt = score_small[v1] + sscore_small[v1] + score_small[v2] +
     sscore_small[v2]; int rand_num = rand() % tt; if(rand_num < score_small[v1] +
     sscore_small[v1]) best_var = v1; else best_var = v2;
                  }
          }*/
  else
  {
    /********BMS********/
    // if() {printf("wrong else\n");
    if (mark_which == 1 || mark_which == 3)
    {
      int bms;
      if (clause_lit_count[sel_c] <= 200)
      {
        bms = (clause_lit_count[sel_c] - 1) / 2 +
              1; // 选择子句的变量个数除2，向上取整
      }
      else
      {
        bms = 100;
      }

      best_var = clause_lit_small[sel_c][rand() % clause_lit_count[sel_c]].var_num;
      for (i = 1; i < bms; i++)
      {
        v = clause_lit_small[sel_c][rand() % clause_lit_count[sel_c]].var_num;
        if (score_small[v] + sscore_small[v] > score_small[best_var] + sscore_small[best_var])
          best_var = v;
        else if (score_small[v] + sscore_small[v] == score_small[best_var] + sscore_small[best_var])
        {
          if (hhscore_small[v] > hhscore_small[best_var])
          {
            best_var = v;
          }
          else if (hhscore_small[v] == hhscore_small[best_var])
          {
            rand_select = rand() % 2;
            if (rand_select == 1)
            {
              best_var = v;
            }
          }
        }
      }
    }
    else
    {
      best_var =
          clause_lit_small[sel_c_set[0]][rand() % clause_lit_count[sel_c_set[0]]]
              .var_num;
      for (j = 0; j < 100; j++)
      {
        // int bms = (clause_lit_count[sel_c_set[j]] - 1) / 2 + 1;
        // //选择子句的变量个数除2，向上取整 best_var = clause_lit_small[sel_c][rand()
        // % clause_lit_count[sel_c]].var_num;
        int bms;
        if (clause_lit_count[sel_c] <= 200)
        {
          bms = (clause_lit_count[sel_c] - 1) / 2 +
                1; // 选择子句的变量个数除2，向上取整
        }
        else
        {
          bms = 100;
        }
        for (i = 0; i < bms; i++)
        {
          v = clause_lit_small[sel_c_set[j]][rand() % clause_lit_count[sel_c_set[j]]]
                  .var_num;
          if (score_small[v] + sscore_small[v] > score_small[best_var] + sscore_small[best_var])
            best_var = v;
          else if (score_small[v] + sscore_small[v] == score_small[best_var] + sscore_small[best_var])
          {
            if (hhscore_small[v] > hhscore_small[best_var])
            {
              best_var = v;
            }
            else if (hhscore_small[v] == hhscore_small[best_var])
            {
              rand_select = rand() % 2;
              if (rand_select == 1)
              {
                best_var = v;
              }
            }
          }
        }
      }
    }
  }
  /********BMS********/

  /*best_var = clause_lit_small[sel_c][0].var_num;
  p = clause_lit_small[sel_c];
  for (p++; (v = p->var_num) != 0; p++)
  {
          if (score_small[v] + sscore_small[v] > score_small[best_var] + sscore_small[best_var])
                  best_var = v;
          else if (score_small[v] + sscore_small[v] == score_small[best_var] + sscore_small[best_var])
          {
                  if(hhscore_small[v] > hhscore_small[best_var])
                  {
                          best_var = v;
                  }else if(hhscore_small[v] == hhscore_small[best_var])
                  {
                          rand_select = rand() % 2;
                          if(rand_select == 1)
                          {
                                  best_var = v;
                          }
                  }
          }
  }*/
  return best_var;
}

void Satlike::flip_fps_small(
    int flipvar) // /*New Added：根据flip2进行了修改*/ 试探性假翻转！
{
  int i, v, c;
  int index;
  lit_small *clause_c;
  long long weight;
  long long gap;

  double org_flipvar_score = score_small[flipvar];
  double org_sscore = sscore_small[flipvar];
  double org_hhscore = hhscore_small[flipvar]; /*待翻转变量的软子句得分*/
  cur_soln[flipvar] = 1 - cur_soln[flipvar];   // 翻转变量flipvar

  for (i = 0; i < var_neighbor_count[flipvar];
       i++)
  { // score2和sscore2临时记录flipvar的所有邻居得分
    score2_small[var_neighbor[flipvar][i]] = score_small[var_neighbor[flipvar][i]];
    sscore2_small[var_neighbor[flipvar][i]] = sscore_small[var_neighbor[flipvar][i]];
    hhscore2_small[var_neighbor[flipvar][i]] = hhscore_small[var_neighbor[flipvar][i]];
  }

  for (i = 0; i < var_lit_count[flipvar]; i++) /*New Added*/
  {
    c = var_lit_small[flipvar][i].clause_num;
    sat_count2_small[c] = sat_count_small[c];
  }

  for (i = 0; i < var_lit_count[flipvar]; ++i) // 对于flipvar的每一个文字
  {
    c = var_lit_small[flipvar][i].clause_num;
    clause_c = clause_lit_small[c];
    weight = var_lit_small[flipvar][i].weight;

    if (org_clause_weight_small[c] == top_clause_weight_small) // 硬子句c
    {
      if (cur_soln[flipvar] ==
          var_lit_small[flipvar][i]
              .sense) // （翻转完后）当前解中变量flipvar的值，等于变量文字数组中变量flipvar的第i个文字的属性【翻转变量flipvar满足】
      {
        // if (org_clause_weight_small[c] != top_clause_weight_small && sat_count_small[c] <
        // clause_true_lit_thres_small[c]) //？？？冗余，可以删除
        // {
        // 	//soft_unsat_weight是否需要复制？
        // 	soft_unsat_weight_small -= org_unit_weight_small[c] * min(weight,
        // clause_true_lit_thres_small[c] - sat_count_small[c]);
        // }
        // sat_count_small[c] += weight;
        if (sat_count2_small[c] + weight <=
            clause_true_lit_thres_small
                [c]) // 若硬子句c的满足计数+变量flipvar的第i个文字的权重<=硬子句c的度
        {
          gap = clause_true_lit_thres_small[c] -
                sat_count2_small[c]; // gap，置为硬子句c的度-硬子句c的满足计数
          for (
              lit_small *p = clause_c; (v = p->var_num) != 0;
              p++) // 对于硬子句c的每个文字p（对应变量v）（根据翻转flipvar后的结果，更新硬子句c中所有变量的得分）
          {
            if (p->sense !=
                cur_soln
                    [v]) // 若文字p的属性，不等于当前解中变量v的值【变量p不满足】
            {
              score2_small[v] -=
                  double((tuned_degree_unit_weight_small[c] *
                          (min(gap, p->weight) -
                           min(gap - weight, p->weight)))); // 变量v的硬子句得分，累积减去(硬子句c的单元权重*(min(gap,
                                                            // 文字p的权重)-min(gap-文字i的权重,
                                                            // 文字p的权重)))
              hhscore2_small[v] += (1 * (max(p->weight - gap + weight, 0LL) -
                                         max(p->weight - gap, 0LL)));
            }
          }
        }
        else if (sat_count2_small[c] <=
                 clause_true_lit_thres_small[c]) // sat_count_small[c]+weight >
                                                 // clause_true_lit_thres_small[c]
        {
          gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score2_small[v] -=
                  double((tuned_degree_unit_weight_small[c] * min(gap, p->weight)));
              // hhscore_small[v] += (unit_weight_small[c] * (min(p->weight, gap1_small[c] -
              // sat_count_small[c] - weight) - max(p->weight - gap, 0)));//2 unsat_small
              hhscore2_small[v] +=
                  (1 * (min(p->weight, gap1_small[c] - sat_count2_small[c] - weight) -
                        max(p->weight - gap, 0LL))); // 2 unsat_small
            }
            else
            {
              score2_small[v] +=
                  double(tuned_degree_unit_weight_small[c] *
                         (p->weight - max(0LL, gap - weight + p->weight)));
              // hhscore_small[v] -= unit_weight_small[c] * min(p->weight, weight - gap);//2
              // sat_small
              hhscore2_small[v] -= 1 * min(p->weight, weight - gap); // 2 sat_small
            }
          }
        }
        else // sat_count_small[c]+weight > clause_true_lit_thres_small[c], sat_count_small[c] >
             // clause_true_lit_thres_small[c]
        {
          /**************hhscore_small****************/
          // ��ǰ��satL>k�Լ�satL+weight>k�����
          if (sat_count2_small[c] <= gap1_small[c]) // ע��Ⱥ� (2)
          {
            // gap = clause_true_lit_thres_small[c] - sat_count_small[c];
            if (sat_count2_small[c] + weight <= gap1_small[c]) // ע��Ⱥ�  ��ǰ�ǣ�2��-��2��
            {
              gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
              for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score2_small[v] += double(tuned_degree_unit_weight_small[c] *
                                            (max(0LL, gap + p->weight) -
                                             max(0LL, gap - weight + p->weight)));
                  // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, -gap) -
                  // min(p->weight, weight - gap));//4
                  hhscore2_small[v] += 1 * (min(p->weight, -gap) -
                                            min(p->weight, weight - gap)); // 4
                }
                else
                {
                  // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, gap1_small[c] -
                  // sat_count_small[c] - weight) - min(p->weight, gap1_small[c] -
                  // sat_count_small[c]));//3
                  hhscore2_small[v] +=
                      1 * (min(p->weight, gap1_small[c] - sat_count2_small[c] - weight) -
                           min(p->weight, gap1_small[c] - sat_count2_small[c])); // 3
                }
              }
            }
            else if (sat_count2_small[c] + weight > gap1_small[c]) //(2)-(3)
            {
              gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
              for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score2_small[v] += double(tuned_degree_unit_weight_small[c] *
                                            (max(0LL, gap + p->weight) -
                                             max(0LL, gap - weight + p->weight)));
                  // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, -gap) -
                  // max(p->weight - weight - sat_count_small[c] + gap , 0));//5
                  hhscore2_small[v] +=
                      1 *
                      (min(p->weight, -gap) -
                       max(p->weight - weight - sat_count2_small[c] + gap, 0LL)); // 5
                }
                else
                {
                  // hhscore_small[v] -= unit_weight_small[c] * (min(p->weight, gap1_small[c] -
                  // sat_count_small[c]));//6
                  hhscore2_small[v] -=
                      1 * (min(p->weight, gap1_small[c] - sat_count2_small[c])); // 6
                }
              }
            }
          }
          else if (sat_count2_small[c] > gap1_small[c]) //(3) - (3)
          {
            gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
            for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
            {
              if (p->sense == cur_soln[v])
              {
                score2_small[v] += double(tuned_degree_unit_weight_small[c] *
                                          (max(0LL, gap + p->weight) -
                                           max(0LL, gap - weight + p->weight)));
                // hhscore_small[v] += unit_weight_small[c] * (max(p->weight - sat_count_small[c]
                // + gap1_small[c] , 0) - max(p->weight - sat_count_small[c] - weight +
                // gap1_small[c], 0));//7
                hhscore2_small[v] +=
                    1 * (max(p->weight - sat_count2_small[c] + gap1_small[c], 0LL) -
                         max(p->weight - sat_count2_small[c] - weight + gap1_small[c],
                             0LL)); // 7
              }
            }
          }
        }
        sat_count2_small[c] += weight;
        /*New Added*/ // 硬子句c的满足计数，累积加上文字i的权重
      }
      else // （翻转后）cur_soln[flipvar] != cur_lit.sense
      {
        //--sat_count_small[c];
        // if (org_clause_weight_small[c] != top_clause_weight_small && sat_count_small[c] -
        // weight < clause_true_lit_thres_small[c]) //？？？
        // {
        // 	//soft_unsat_weight是否需要复制？
        // 	soft_unsat_weight_small += org_unit_weight_small[c] * min(weight,
        // clause_true_lit_thres_small[c] - sat_count_small[c] + weight);
        // }

        if (sat_count2_small[c] - weight >= clause_true_lit_thres_small[c])
        {
          // gap = clause_true_lit_thres_small[c] - sat_count_small[c];
          /***************hhscore_small*************/
          if (sat_count2_small[c] > gap1_small[c]) //(3)
          {
            if (sat_count2_small[c] - weight > gap1_small[c]) //(3) - (3)  ע��Ⱥ�
            {
              gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
              for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score2_small[v] -= double(tuned_degree_unit_weight_small[c] *
                                            (max(0LL, gap + weight + p->weight) -
                                             max(0LL, gap + p->weight)));
                  // hhscore_small[v] += unit_weight_small[c] * (max(p->weight -
                  // sat_count_small[c] + gap1_small[c], 0) - max(p->weight - sat_count_small[c] +
                  // weight + gap1_small[c], 0));//8
                  hhscore2_small[v] +=
                      1 * (max(p->weight - sat_count2_small[c] + gap1_small[c], 0LL) -
                           max(p->weight - sat_count2_small[c] + weight + gap1_small[c],
                               0LL)); // 8
                }
              }
            }
            else if (sat_count2_small[c] - weight <= gap1_small[c]) //(3) - (2)
            {
              gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
              for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score2_small[v] -= double(tuned_degree_unit_weight_small[c] *
                                            (max(0LL, gap + weight + p->weight) -
                                             max(0LL, gap + p->weight)));
                  // hhscore_small[v] += unit_weight_small[c] * (max(p->weight -
                  // sat_count_small[c] + gap1_small[c], 0) - min(p->weight, sat_count_small[c] -
                  // weight - sat_count_small[c]));//9
                  hhscore2_small[v] +=
                      1 * (max(p->weight - sat_count2_small[c] + gap1_small[c], 0LL) -
                           min(p->weight,
                               sat_count2_small[c] - weight - sat_count2_small[c])); // 9
                }
                else
                {
                  // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, gap1_small[c] -
                  // sat_count_small[c] + weight));//10
                  hhscore2_small[v] +=
                      1 *
                      (min(p->weight, gap1_small[c] - sat_count2_small[c] + weight)); // 10
                }
              }
            }
          }
          else if (sat_count2_small[c] <= gap1_small[c]) //(2) - (2)
          {
            gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
            for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
            {
              if (p->sense == cur_soln[v])
              {
                score2_small[v] -= double(tuned_degree_unit_weight_small[c] *
                                          (max(0LL, gap + weight + p->weight) -
                                           max(0LL, gap + p->weight)));
                // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, -gap) -
                // min(p->weight, sat_count_small[c] - weight -
                // clause_true_lit_thres_small[c]));//11
                hhscore2_small[v] +=
                    1 * (min(p->weight, -gap) -
                         min(p->weight, sat_count2_small[c] - weight -
                                            clause_true_lit_thres_small[c])); // 11
              }
              else
              {
                // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, gap1_small[c] -
                // sat_count_small[c] + weight) - min(p->weight, gap1_small[c] -
                // sat_count_small[c]));//12
                hhscore2_small[v] +=
                    1 * (min(p->weight, gap1_small[c] - sat_count2_small[c] + weight) -
                         min(p->weight, gap1_small[c] - sat_count2_small[c])); // 12
              }
            }
          }
          /*gap = clause_true_lit_thres_small[c] - sat_count_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
                  if (p->sense == cur_soln[v])
                  {
                          score_small[v] -= unit_weight_small[c] * (max(0, gap + weight +
          p->weight) - max(0, gap + p->weight));
                  }
          }*/
        }
        else if (sat_count2_small[c] >= clause_true_lit_thres_small[c]) //(2) -(1) ע��Ⱥ�
        {
          gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense == cur_soln[v])
            {
              score2_small[v] -= double(tuned_degree_unit_weight_small[c] *
                                        (p->weight - max(0LL, gap + p->weight)));
              // hhscore_small[v] += unit_weight_small[c] * (p->weight, -gap);//13
              hhscore2_small[v] += 1 * (p->weight, -gap); // 13
            }
            else
            {
              score2_small[v] += double(tuned_degree_unit_weight_small[c] *
                                        min(p->weight, gap + weight));
              // hhscore_small[v] += unit_weight_small[c] * (min(p->weight - gap - weight,
              // 0) - min(p->weight, gap1_small[c] - sat_count_small[c]));//14
              hhscore2_small[v] +=
                  1 * (min(p->weight - gap - weight, 0LL) -
                       min(p->weight, gap1_small[c] - sat_count2_small[c])); // 14
            }
          }
        }
        else //(1) -(1)
        {
          gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score2_small[v] +=
                  double(tuned_degree_unit_weight_small[c] *
                         (min(p->weight, gap + weight) - min(p->weight, gap)));
              // hhscore_small[v] += unit_weight_small[c] * (max(p->weight - gap - weight,
              // 0) - max(p->weight - gap, 0));//15
              hhscore2_small[v] += 1 * (max(p->weight - gap - weight, 0LL) -
                                        max(p->weight - gap, 0LL)); // 15
            }
          }
        }
        // if (sat_count_small[c] >= clause_true_lit_thres_small[c] && sat_count_small[c] - weight
        // < clause_true_lit_thres_small[c])
        // {
        // 	unsat_small(c); //硬子句c不满足
        // }
        sat_count2_small[c] -= weight;
        /*New Added*/ // 硬子句c的满足计数，累积减去文字i的权重

      } // end else
    }
    // else //软子句
    // {
    // 	if (cur_soln[flipvar] == var_lit_small[flipvar][i].sense)
    // 	{
    // 		// if (org_clause_weight_small[c] != top_clause_weight_small && sat_count_small[c]
    // < clause_true_lit_thres_small[c])
    // 		// {
    // 		// 	//soft_unsat_weight是否需要复制？
    // 		// 	soft_unsat_weight_small -= org_unit_weight_small[c] * min(weight,
    // clause_true_lit_thres_small[c] - sat_count_small[c]);
    // //不满足的软子句权重，累积减去(软子句c的初始单元权重*min(文字i的权重,
    // 软子句c的度-软子句c的满足计数))
    // 		// }
    // 		//sat_count_small[c] += weight;

    // 		if (sat_count2_small[c] + weight <= clause_true_lit_thres_small[c])
    // //若软子句c的满足计数+变量flipvar的第i个文字的权重<=软子句c的度
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore2_small[v] -= (unit_weight_small[c] *
    // (min(gap, p->weight) - min(gap - weight, p->weight)));
    // 				}
    // 			}
    // 		}
    // 		else if (sat_count2_small[c] <= clause_true_lit_thres_small[c])
    // //sat_count_small[c]+weight > clause_true_lit_thres_small[c]
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore2_small[v] -= (unit_weight_small[c] * min(gap,
    // p->weight));
    // 				}
    // 				else
    // 				{
    // 					sscore2_small[v] += unit_weight_small[c] *
    // (p->weight - max(0, gap - weight + p->weight));
    // 				}
    // 			}
    // 		}
    // 		else //sat_count_small[c]+weight > clause_true_lit_thres_small[c],
    // sat_count_small[c] > clause_true_lit_thres_small[c]
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore2_small[v] += unit_weight_small[c] * (max(0,
    // gap + p->weight) - max(0, gap - weight + p->weight));
    // 				}
    // 			}
    // 		}
    // 		// if (sat_count_small[c] < clause_true_lit_thres_small[c] && sat_count_small[c] +
    // weight >= clause_true_lit_thres_small[c])
    // 		// {
    // 		// 	sat_small(c);
    // 		// }
    // 		sat_count2_small[c] += weight;  /*New Added*/
    // 	}
    // 	else // cur_soln[flipvar] != cur_lit.sense
    // 	{
    // 		//--sat_count_small[c];
    // 		// if (org_clause_weight_small[c] != top_clause_weight_small && sat_count_small[c]
    // - weight < clause_true_lit_thres_small[c])
    // 		// {
    // 		// 	//soft_unsat_weight是否需要复制
    // 		// 	soft_unsat_weight_small += org_unit_weight_small[c] * min(weight,
    // clause_true_lit_thres_small[c] - sat_count_small[c] + weight);
    // 		// }

    // 		if (sat_count2_small[c] - weight >= clause_true_lit_thres_small[c])
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore2_small[v] -= unit_weight_small[c] * (max(0,
    // gap + weight + p->weight) - max(0, gap + p->weight));
    // 				}
    // 			}
    // 		}
    // 		else if (sat_count2_small[c] >= clause_true_lit_thres_small[c])
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore2_small[v] -= unit_weight_small[c] *
    // (p->weight - max(0, gap + p->weight));
    // 				}
    // 				else
    // 				{
    // 					sscore2_small[v] += unit_weight_small[c] *
    // min(p->weight, gap + weight);
    // 				}
    // 			}
    // 		}
    // 		else
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count2_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore2_small[v] += unit_weight_small[c] *
    // (min(p->weight, gap + weight) - min(p->weight, gap));
    // 				}
    // 			}
    // 		}
    // 		// if (sat_count_small[c] >= clause_true_lit_thres_small[c] && sat_count_small[c]
    // - weight < clause_true_lit_thres_small[c])
    // 		// {
    // 		// 	unsat_small(c);
    // 		// }
    // 		sat_count2_small[c] -= weight;    /*New Added*/

    // 	} //end else
    // }
  }

  // update information of flipvar
  cur_soln[flipvar] = 1 - cur_soln[flipvar]; // 复原？
  score2_small[flipvar] = -org_flipvar_score;
  sscore2_small[flipvar] = -org_sscore;
  hhscore2_small[flipvar] = -org_hhscore;
  update_goodvarstack12_small(flipvar);
}

void Satlike::update_goodvarstack12_small(int flipvar) // New Added
{
  int v;
  goodvar_stack2_num = 0;
  // remove the vars no longer goodvar in goodvar stack
  // add goodvar
  for (int i = 0; i < var_neighbor_count[flipvar]; ++i)
  {
    v = var_neighbor[flipvar][i];
    if (score2_small[v] + sscore2_small[v] > 0) /*New Added*/
    {
      goodvar_stack2[goodvar_stack2_num] = v;
      goodvar_stack2_num++;
    }
  }
}

void Satlike::update_goodvarstack1_small(int flipvar)
{
  int v;

  // remove the vars no longer goodvar in goodvar stack
  for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
  {
    v = goodvar_stack[index];
    if (score_small[v] + sscore_small[v] <= 0)
    // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v] <= 0)
    {
      int top_v = mypop(goodvar_stack);
      goodvar_stack[index] = top_v;
      already_in_goodvar_stack[top_v] = index;
      already_in_goodvar_stack[v] = -1;
    }
  }

  // add goodvar
  for (int i = 0; i < var_neighbor_count[flipvar]; ++i)
  {
    v = var_neighbor[flipvar][i];
    if (score_small[v] + sscore_small[v] > 0)
    // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v] > 0)
    {
      if (already_in_goodvar_stack[v] == -1)
      {
        already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
        mypush(v, goodvar_stack);
      }
    }
  }
}
void Satlike::update_goodvarstack2_small(int flipvar)
{
  if (score_small[flipvar] > 0 && already_in_goodvar_stack[flipvar] == -1)
  {
    already_in_goodvar_stack[flipvar] = goodvar_stack_fill_pointer;
    mypush(flipvar, goodvar_stack);
  }
  else if (score_small[flipvar] <= 0 && already_in_goodvar_stack[flipvar] != -1)
  {
    int index = already_in_goodvar_stack[flipvar];
    int last_v = mypop(goodvar_stack);
    goodvar_stack[index] = last_v;
    already_in_goodvar_stack[last_v] = index;
    already_in_goodvar_stack[flipvar] = -1;
  }
  int i, v;
  for (i = 0; i < var_neighbor_count[flipvar]; ++i)
  {
    v = var_neighbor[flipvar][i];
    if (score_small[v] > 0)
    {
      if (already_in_goodvar_stack[v] == -1)
      {
        already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
        mypush(v, goodvar_stack);
      }
    }
    else if (already_in_goodvar_stack[v] != -1)
    {
      int index = already_in_goodvar_stack[v];
      int last_v = mypop(goodvar_stack);
      goodvar_stack[index] = last_v;
      already_in_goodvar_stack[last_v] = index;
      already_in_goodvar_stack[v] = -1;
    }
  }
}

void Satlike::flip_small(int flipvar)
{
  int i, v, c;
  int index;
  lit_small *clause_c;
  long long weight;
  long long gap;

  double org_flipvar_score = score_small[flipvar];
  double org_sscore = sscore_small[flipvar];
  double org_hhscore = hhscore_small[flipvar]; // hhscore_small
  cur_soln[flipvar] = 1 - cur_soln[flipvar];

  // cout<<"filpvar = "<<flipvar<<endl;

  for (i = 0; i < var_lit_count[flipvar]; ++i)
  {
    c = var_lit_small[flipvar][i].clause_num;
    clause_c = clause_lit_small[c];
    weight = var_lit_small[flipvar][i].weight;
    if (org_clause_weight_small[c] == top_clause_weight_small)
    {
      if (cur_soln[flipvar] ==
          var_lit_small[flipvar][i].sense) // SatL1 = SatL + weight
      {
        if (sat_count_small[c] < clause_true_lit_thres_small[c] &&
            sat_count_small[c] + weight < clause_true_lit_thres_small[c]) // zyj
        {
          // hard_unsat_weight_small -= double(avghard[c] * weight);
          hard_unsat_weight_small -= weight;
        }
        else if (sat_count_small[c] < clause_true_lit_thres_small[c] &&
                 sat_count_small[c] + weight >= clause_true_lit_thres_small[c])
        {
          // hard_unsat_weight_small -= double(avghard[c] * (clause_true_lit_thres_small[c]
          // - sat_count_small[c]));
          hard_unsat_weight_small -= (clause_true_lit_thres_small[c] - sat_count_small[c]);
        }

        if (sat_count_small[c] + weight <= clause_true_lit_thres_small[c])
        {
          gap = clause_true_lit_thres_small[c] - sat_count_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score_small[v] -= double(
                  (tuned_degree_unit_weight_small[c] *
                   (min(gap, p->weight) - min(gap - weight, p->weight))));
              // hhscore_small[v] += (unit_weight_small[c] * (max(p->weight - gap + weight,
              // 0) - max(p->weight - gap , 0)));//1
              hhscore_small[v] += (1 * (max(p->weight - gap + weight, 0LL) -
                                        max(p->weight - gap, 0LL))); // 1
            }
          }
        }
        else if (sat_count_small[c] <=
                 clause_true_lit_thres_small[c]) // sat_count_small[c]+weight >
                                                 // clause_true_lit_thres_small[c]
        {
          gap = clause_true_lit_thres_small[c] - sat_count_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score_small[v] -=
                  double((tuned_degree_unit_weight_small[c] * min(gap, p->weight)));
              // hhscore_small[v] += (unit_weight_small[c] * (min(p->weight, gap1_small[c] -
              // sat_count_small[c] - weight) - max(p->weight - gap, 0)));//2 unsat_small
              hhscore_small[v] +=
                  (1 * (min(p->weight, gap1_small[c] - sat_count_small[c] - weight) -
                        max(p->weight - gap, 0LL))); // 2 unsat_small
            }
            else
            {
              score_small[v] +=
                  double(tuned_degree_unit_weight_small[c] *
                         (p->weight - max(0LL, gap - weight + p->weight)));
              // hhscore_small[v] -= unit_weight_small[c] * min(p->weight, weight - gap);//2
              // sat_small
              hhscore_small[v] -= 1 * min(p->weight, weight - gap); // 2 sat_small
            }
          }
        }
        else // sat_count_small[c]+weight > clause_true_lit_thres_small[c], sat_count_small[c] >
             // clause_true_lit_thres_small[c]
        {
          /**************hhscore_small****************/
          // ��ǰ��satL>k�Լ�satL+weight>k�����
          if (sat_count_small[c] <= gap1_small[c]) // ע��Ⱥ� (2)
          {
            // gap = clause_true_lit_thres_small[c] - sat_count_small[c];
            if (sat_count_small[c] + weight <= gap1_small[c]) // ע��Ⱥ�  ��ǰ�ǣ�2��-��2��
            {
              gap = clause_true_lit_thres_small[c] - sat_count_small[c];
              for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score_small[v] += double(tuned_degree_unit_weight_small[c] *
                                           (max(0LL, gap + p->weight) -
                                            max(0LL, gap - weight + p->weight)));
                  // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, -gap) -
                  // min(p->weight, weight - gap));//4
                  hhscore_small[v] += 1 * (min(p->weight, -gap) -
                                           min(p->weight, weight - gap)); // 4
                }
                else
                {
                  // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, gap1_small[c] -
                  // sat_count_small[c] - weight) - min(p->weight, gap1_small[c] -
                  // sat_count_small[c]));//3
                  hhscore_small[v] +=
                      1 * (min(p->weight, gap1_small[c] - sat_count_small[c] - weight) -
                           min(p->weight, gap1_small[c] - sat_count_small[c])); // 3
                }
              }
            }
            else if (sat_count_small[c] + weight > gap1_small[c]) //(2)-(3)
            {
              gap = clause_true_lit_thres_small[c] - sat_count_small[c];
              for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score_small[v] += double(tuned_degree_unit_weight_small[c] *
                                           (max(0LL, gap + p->weight) -
                                            max(0LL, gap - weight + p->weight)));
                  // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, -gap) -
                  // max(p->weight - weight - sat_count_small[c] + gap , 0));//5
                  hhscore_small[v] +=
                      1 *
                      (min(p->weight, -gap) -
                       max(p->weight - weight - sat_count_small[c] + gap, 0LL)); // 5
                }
                else
                {
                  // hhscore_small[v] -= unit_weight_small[c] * (min(p->weight, gap1_small[c] -
                  // sat_count_small[c]));//6
                  hhscore_small[v] -=
                      1 * (min(p->weight, gap1_small[c] - sat_count_small[c])); // 6
                }
              }
            }
          }
          else if (sat_count_small[c] > gap1_small[c]) //(3) - (3)
          {
            gap = clause_true_lit_thres_small[c] - sat_count_small[c];
            for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
            {
              if (p->sense == cur_soln[v])
              {
                score_small[v] += double(tuned_degree_unit_weight_small[c] *
                                         (max(0LL, gap + p->weight) -
                                          max(0LL, gap - weight + p->weight)));
                // hhscore_small[v] += unit_weight_small[c] * (max(p->weight - sat_count_small[c]
                // + gap1_small[c] , 0) - max(p->weight - sat_count_small[c] - weight +
                // gap1_small[c], 0));//7
                hhscore_small[v] +=
                    1 * (max(p->weight - sat_count_small[c] + gap1_small[c], 0LL) -
                         max(p->weight - sat_count_small[c] - weight + gap1_small[c],
                             0LL)); // 7
              }
            }
          }
        }
        if (sat_count_small[c] < clause_true_lit_thres_small[c] &&
            sat_count_small[c] + weight >= clause_true_lit_thres_small[c])
        {
          sat_small(c);
        }
        sat_count_small[c] += weight;
      }
      else // cur_soln[flipvar] != cur_lit.sense
      {
        if (sat_count_small[c] >= clause_true_lit_thres_small[c] &&
            sat_count_small[c] - weight < clause_true_lit_thres_small[c]) // zyj
        {
          // hard_unsat_weight_small += double(avghard[c] * (clause_true_lit_thres_small[c]
          // - sat_count_small[c] + weight));
          hard_unsat_weight_small +=
              (clause_true_lit_thres_small[c] - sat_count_small[c] + weight);
        }
        else if (sat_count_small[c] < clause_true_lit_thres_small[c] &&
                 sat_count_small[c] - weight < clause_true_lit_thres_small[c])
        {
          // hard_unsat_weight_small += double(avghard[c] * weight);
          hard_unsat_weight_small += weight;
        }

        if (sat_count_small[c] - weight >= clause_true_lit_thres_small[c])
        {
          // gap = clause_true_lit_thres_small[c] - sat_count_small[c];
          /***************hhscore_small*************/
          if (sat_count_small[c] > gap1_small[c]) //(3)
          {
            if (sat_count_small[c] - weight > gap1_small[c]) //(3) - (3)  ע��Ⱥ�
            {
              gap = clause_true_lit_thres_small[c] - sat_count_small[c];
              for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score_small[v] -= double(tuned_degree_unit_weight_small[c] *
                                           (max(0LL, gap + weight + p->weight) -
                                            max(0LL, gap + p->weight)));
                  // hhscore_small[v] += unit_weight_small[c] * (max(p->weight -
                  // sat_count_small[c] + gap1_small[c], 0) - max(p->weight - sat_count_small[c] +
                  // weight + gap1_small[c], 0));//8
                  hhscore_small[v] +=
                      1 * (max(p->weight - sat_count_small[c] + gap1_small[c], 0LL) -
                           max(p->weight - sat_count_small[c] + weight + gap1_small[c],
                               0LL)); // 8
                }
              }
            }
            else if (sat_count_small[c] - weight <= gap1_small[c]) //(3) - (2)
            {
              gap = clause_true_lit_thres_small[c] - sat_count_small[c];
              for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score_small[v] -= double(tuned_degree_unit_weight_small[c] *
                                           (max(0LL, gap + weight + p->weight) -
                                            max(0LL, gap + p->weight)));
                  // hhscore_small[v] += unit_weight_small[c] * (max(p->weight -
                  // sat_count_small[c] + gap1_small[c], 0) - min(p->weight, sat_count_small[c] -
                  // weight - sat_count_small[c]));//9
                  hhscore_small[v] +=
                      1 * (max(p->weight - sat_count_small[c] + gap1_small[c], 0LL) -
                           min(p->weight,
                               sat_count_small[c] - weight - sat_count_small[c])); // 9
                }
                else
                {
                  // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, gap1_small[c] -
                  // sat_count_small[c] + weight));//10
                  hhscore_small[v] +=
                      1 *
                      (min(p->weight, gap1_small[c] - sat_count_small[c] + weight)); // 10
                }
              }
            }
          }
          else if (sat_count_small[c] <= gap1_small[c]) //(2) - (2)
          {
            gap = clause_true_lit_thres_small[c] - sat_count_small[c];
            for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
            {
              if (p->sense == cur_soln[v])
              {
                score_small[v] -= double(tuned_degree_unit_weight_small[c] *
                                         (max(0LL, gap + weight + p->weight) -
                                          max(0LL, gap + p->weight)));
                // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, -gap) -
                // min(p->weight, sat_count_small[c] - weight -
                // clause_true_lit_thres_small[c]));//11
                hhscore_small[v] +=
                    1 * (min(p->weight, -gap) -
                         min(p->weight, sat_count_small[c] - weight -
                                            clause_true_lit_thres_small[c])); // 11
              }
              else
              {
                // hhscore_small[v] += unit_weight_small[c] * (min(p->weight, gap1_small[c] -
                // sat_count_small[c] + weight) - min(p->weight, gap1_small[c] -
                // sat_count_small[c]));//12
                hhscore_small[v] +=
                    1 * (min(p->weight, gap1_small[c] - sat_count_small[c] + weight) -
                         min(p->weight, gap1_small[c] - sat_count_small[c])); // 12
              }
            }
          }
          /*gap = clause_true_lit_thres_small[c] - sat_count_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
                  if (p->sense == cur_soln[v])
                  {
                          score_small[v] -= unit_weight_small[c] * (max(0, gap + weight +
          p->weight) - max(0, gap + p->weight));
                  }
          }*/
        }
        else if (sat_count_small[c] >= clause_true_lit_thres_small[c]) //(2) -(1) ע��Ⱥ�
        {
          gap = clause_true_lit_thres_small[c] - sat_count_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense == cur_soln[v])
            {
              score_small[v] -= double(tuned_degree_unit_weight_small[c] *
                                       (p->weight - max(0LL, gap + p->weight)));
              // hhscore_small[v] += unit_weight_small[c] * (p->weight, -gap);//13
              hhscore_small[v] += 1 * (p->weight, -gap); // 13
            }
            else
            {
              score_small[v] += double(tuned_degree_unit_weight_small[c] *
                                       min(p->weight, gap + weight));
              // hhscore_small[v] += unit_weight_small[c] * (min(p->weight - gap - weight,
              // 0) - min(p->weight, gap1_small[c] - sat_count_small[c]));//14
              hhscore_small[v] += 1 * (min(p->weight - gap - weight, 0LL) -
                                       min(p->weight, gap1_small[c] - sat_count_small[c])); // 14
            }
          }
        }
        else //(1) -(1)
        {
          gap = clause_true_lit_thres_small[c] - sat_count_small[c];
          for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score_small[v] +=
                  double(tuned_degree_unit_weight_small[c] *
                         (min(p->weight, gap + weight) - min(p->weight, gap)));
              // hhscore_small[v] += unit_weight_small[c] * (max(p->weight - gap - weight,
              // 0) - max(p->weight - gap, 0));//15
              hhscore_small[v] += 1 * (max(p->weight - gap - weight, 0LL) -
                                       max(p->weight - gap, 0LL)); // 15
            }
          }
        }
        if (sat_count_small[c] >= clause_true_lit_thres_small[c] &&
            sat_count_small[c] - weight < clause_true_lit_thres_small[c])
        {
          unsat_small(c);
        }
        sat_count_small[c] -= weight;

      } // end else
    }
    // else
    // {
    // 	if (cur_soln[flipvar] == var_lit_small[flipvar][i].sense)
    // 	{
    // 		if (org_clause_weight_small[c] != top_clause_weight_small && sat_count_small[c] <
    // clause_true_lit_thres_small[c])
    // 		{
    // 			soft_unsat_weight_small -= org_unit_weight_small[c] * min(weight,
    // clause_true_lit_thres_small[c] - sat_count_small[c]);
    // 		}
    // 		//sat_count_small[c] += weight;

    // 		if (sat_count_small[c] + weight <= clause_true_lit_thres_small[c])
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore_small[v] -= (unit_weight_small[c] * (min(gap,
    // p->weight) - min(gap - weight, p->weight)));
    // 				}
    // 			}
    // 		}
    // 		else if (sat_count_small[c] <= clause_true_lit_thres_small[c])
    // //sat_count_small[c]+weight > clause_true_lit_thres_small[c]
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore_small[v] -= (unit_weight_small[c] * min(gap,
    // p->weight));
    // 				}
    // 				else
    // 				{
    // 					sscore_small[v] += unit_weight_small[c] * (p->weight
    // - max(0, gap - weight + p->weight));
    // 				}
    // 			}
    // 		}
    // 		else //sat_count_small[c]+weight > clause_true_lit_thres_small[c],
    // sat_count_small[c] > clause_true_lit_thres_small[c]
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore_small[v] += unit_weight_small[c] * (max(0,
    // gap + p->weight) - max(0, gap - weight + p->weight));
    // 				}
    // 			}
    // 		}
    // 		if (sat_count_small[c] < clause_true_lit_thres_small[c] && sat_count_small[c] +
    // weight >= clause_true_lit_thres_small[c])
    // 		{
    // 			sat_small(c);
    // 		}
    // 		sat_count_small[c] += weight;
    // 	}
    // 	else // cur_soln[flipvar] != cur_lit.sense
    // 	{
    // 		//--sat_count_small[c];
    // 		if (org_clause_weight_small[c] != top_clause_weight_small && sat_count_small[c] -
    // weight < clause_true_lit_thres_small[c])
    // 		{
    // 			soft_unsat_weight_small += org_unit_weight_small[c] * min(weight,
    // clause_true_lit_thres_small[c] - sat_count_small[c] + weight);
    // 		}

    // 		if (sat_count_small[c] - weight >= clause_true_lit_thres_small[c])
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore_small[v] -= unit_weight_small[c] * (max(0,
    // gap + weight + p->weight) - max(0, gap + p->weight));
    // 				}
    // 			}
    // 		}
    // 		else if (sat_count_small[c] >= clause_true_lit_thres_small[c])
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore_small[v] -= unit_weight_small[c] * (p->weight
    // - max(0, gap + p->weight));
    // 				}
    // 				else
    // 				{
    // 					sscore_small[v] += unit_weight_small[c] *
    // min(p->weight, gap + weight);
    // 				}
    // 			}
    // 		}
    // 		else
    // 		{
    // 			gap = clause_true_lit_thres_small[c] - sat_count_small[c];
    // 			for (lit_small *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore_small[v] += unit_weight_small[c] *
    // (min(p->weight, gap + weight) - min(p->weight, gap));
    // 				}
    // 			}
    // 		}
    // 		if (sat_count_small[c] >= clause_true_lit_thres_small[c] && sat_count_small[c] -
    // weight < clause_true_lit_thres_small[c])
    // 		{
    // 			unsat_small(c);
    // 		}
    // 		sat_count_small[c] -= weight;

    // 	} //end else
    // }
    else // Nupbo
    {
      if (cur_soln[flipvar] == var_lit_small[flipvar][i].sense) // flip_small better
      {
        soft_unsat_weight_small -= org_clause_weight_small[c];
        sat_small(c);
        sat_count_small[c] += weight;
      }
      else // flip_small worse
      {
        soft_unsat_weight_small += org_clause_weight_small[c];
        unsat_small(c);
        sat_count_small[c] -= weight;
      } // end else
    }
  }

  // update information of flipvar
  score_small[flipvar] = -org_flipvar_score;
  sscore_small[flipvar] = -org_sscore;
  hhscore_small[flipvar] = -org_hhscore; // hhscore_small
  update_goodvarstack1_small(flipvar);
  // for(int i = 1;i <= num_vars; i++)
  // {
  // 	cout<<"hhscore_small "<<i<<" = "<<hhscore_small[i]<<endl;
  // }
}

void Satlike::local_search_small(vector<int> &init_solution)
{
  settings_small();
  max_flips = 200000000;
  init_small(init_solution);
  cout << "time is " << get_runtime() << endl;
  cout << "hard unsat_small nb is " << hard_unsat_nb << endl;
  cout << "soft unsat_small nb is " << soft_unsat_weight_small << endl;
  cout << "goodvar nb is " << goodvar_stack_fill_pointer << endl;
}

void Satlike::print_best_solution() // 传入文件名和seed
{
  if (best_soln_feasible == 1)
  {
    if ((intsize <= 63) || (intsize > 63))
    {
      cout << "s SATISFIABLE" << endl;
#ifdef USEPRESOLVE
      if (intsize <= 63 && use_presolve)
      {
        if (prob.getConstraintMatrix().getNCols() > 0 || opt_dec_model)
        {
          postsolve_solution(false, true);
        }
        else
          postsolve_solution(true, true);
      }
      else
      {
#endif
        /*cout << "v " << flush;
        for (int i = 1; i <= num_vars; ++i)
        {
          if (best_soln[i] == 0)
            cout << "-x" << i << " ";
          else
            cout << 'x' << i << " ";
        }
        cout << endl;*/
        constexpr int BUF_SIZE = 50000;
        static char buf[BUF_SIZE];
        static int lst = 0;
        // buf[0] = '\n';
        // buf[1] = 'v';
        buf[0] = 'v';
        // lst += 2;
        lst += 1;
        for (int i = 1; i <= num_vars; i++)
        {
          std::string str = "x" + std::to_string(i);
          const char *cstr = str.c_str();
          int sz = strlen(cstr);
          if (lst + sz + 2 >= BUF_SIZE)
          {
            buf[lst++] = '\n';
            lst = write(1, buf, lst);
            buf[0] = 'v';
            lst = 1;
          }
          buf[lst++] = ' ';
          if (best_soln[i] == 0)
            buf[lst++] = '-';
          strcpy(buf + lst, cstr);
          lst += sz;
        }
        buf[lst++] = '\n';
        lst = write(1, buf, lst);
        lst = 0;
#ifdef USEPRESOLVE
      }
#endif
      cout << "c Done " << opt_time << "s" << endl;
    }
    else
    {
      cout << "c verify solution wrong " << endl;
      cout << "s UNKNOWN" << endl;
    }
  }
  else
    cout << "s UNKNOWN" << endl;
}

void Satlike::cal_solution_small() // 传入文件名和seed
{
  // long long verify_unsat_weight = 0;
  realobj_small = 0;
  int c;

  if (best_soln_feasible == 1)
  {
    for (c = 0; c < num_clauses; ++c)
    {
      if (org_clause_weight_small[c] != top_clause_weight_small)
      {
        if (clause_lit_small[c][0].sense == 0)
        {
          realobj_small += org_clause_weight_small[c] * best_soln[clause_lit_small[c][0].var_num];
        }
        else
        {
          realobj_small -= org_clause_weight_small[c] * best_soln[clause_lit_small[c][0].var_num];
        }
      }
    }
  }
}

void Satlike::local_search_with_decimation_small(vector<int> &init_solution,
                                                 char *inputfile)
{
  printf("c Use LS-small\n");
  int step_count = 0;        // wyy-20221213
  int cur_hard_unsat_nb = 0; // wyy-20221213-1
  int xishu;
  // int MABh_step = 0;

  if (num_vars < 1800000)
    xishu = 1;
  else
    xishu = 16;

  settings_small();
  for (tries = 1; tries < max_tries; ++tries)
  {
    init_small(init_solution);
    cur_hard_unsat_nb = hard_unsat_nb; // wyy-20221213-1
    for (step = 1; step < max_flips; ++step)
    {
      step_count++;
      // MABh_step++;
      if (hard_unsat_nb < cur_hard_unsat_nb)
      {                                    // wyy-20221213-1
        cur_hard_unsat_nb = hard_unsat_nb; // wyy-20221213-1
        step_count = step_count / 2 + 1;
      }
      if (hard_unsat_nb == 0 && (soft_unsat_weight_small < opt_unsat_weight_small || best_soln_feasible == 0))
      {
        if (soft_unsat_weight_small < top_clause_weight_small)
        {
          // softclause_weight_threshold += 0;
          best_soln_feasible = 1;
          opt_unsat_weight_small = soft_unsat_weight_small;
          step_count = 0;
          opt_time = get_runtime();
          // printf("opt_unsat_weight_small = %lld, opt_time = %.2f, step = %lld\n",
          // opt_unsat_weight_small, opt_time, step);
          for (int v = 1; v <= num_vars; ++v)
            best_soln[v] = cur_soln[v];
          cal_solution_small();
#ifdef USEPRESOLVE
          if (!opt_dec_model) // opt
          {
            if (use_presolve)
              postsolve_solution(true, false);
            else
            {
              if (realobj_small < opt_realobj_small)
              {
                opt_realobj_small = realobj_small;
                printf("o %lld\n", realobj_small);
              }
            }
          }
          else
          {
            ;
          }
#else
          if (!opt_dec_model)
          {
            if (realobj_small < opt_realobj_small)
            {
              opt_realobj_small = realobj_small;
              printf("o %lld\n", realobj_small);
            }
          }
#endif
          if (opt_unsat_weight_small == 0)
          {
            return;
          }
        }
        cur_hard_unsat_nb = num_hclauses; // wyy-20221213-1
        if (num_vars < 1800000 && xishu != 1)
          xishu = xishu / 2; // wyy-20221213-1
        else if (num_vars >= 1800000 && xishu != 16)
          xishu = xishu / 2;
      }

      // double elapse_time = get_runtime();
      // if (elapse_time >= cutoff_time)
      // {
      //   return;
      // }

      if (goodvar_stack_fill_pointer > 0)
      { // 选择变量，翻转变量
        int flipvar = pick_var_small();
        flip_small(flipvar);
        time_stamp[flipvar] = step;
      }
      else
      {
        // cout<<"???"<<endl;
        pick_vars_small();
      }
      if ((step_count % (100000 * xishu)) == (100000 * xishu - 1)) // 一万 十万
      {
        // printf("----turb_small begin------------------------------\n");
        // printf("hard_unsat_nb = %d, run time =%.2f
        // \n",hard_unsat_nb,get_runtime());
        if (hard_unsat_nb <= 10 && rand() % 100 < 50)
        {
          turb_small();
          if (xishu <= 100)
            xishu = 2 * xishu;
          // xishu = 36;
        }
        else
        {
          // printf("missing turb_small\n");
          if (best_soln_feasible == 1)
          {
            for (int v = 1; v <= num_vars; ++v)
              cur_soln[v] = best_soln[v];
            init_turb_small();
            turb_small();
          }
        }
        step_count = 0;
        cur_hard_unsat_nb = hard_unsat_nb;
      }
    }
  }
}

void Satlike::turb_small()
{
  // cout<<hard_unsat_nb<<endl;
  /*扰动解*/
  /*1、cur_sol*/
  /*2、候选解集合*/

  /*select clauses*/
  int c, sel_c, v;
  int cur_hard_unsat_nb;
  int count_var_mark, limit_var_mark, flag = 0;
  int turb_flipvar;
  int step_sum = 50;
  selected_var_num = 0;
  // int fix_value = rand() % 2;

  cur_hard_unsat_nb = hard_unsat_nb; // init_small
  memset(turb_hardunsat_stack, 0, num_clauses * sizeof(int));
  memset(is_selected_clauses, 0, num_clauses * sizeof(int));
  memset(selected_var, 0, num_vars * sizeof(int));
  memset(var_mark, 0, num_vars * sizeof(int)); // wyy-20221213-1

  for (c = 0; c < cur_hard_unsat_nb; c++)
  {
    turb_hardunsat_stack[c] = hardunsat_stack[c];
  }
  count_var_mark = 0;               // wyy-20221213
  int theshold = num_vars / 20 + 1; // wyy-20221213
  // printf("cur_hard_unsat_nb=%d\n",cur_hard_unsat_nb);
  if (theshold == 1)
    return;
  if (cur_hard_unsat_nb >= 10) // wyy-20221213  参数10再考虑考虑！
  {
    for (c = 0; c < 10; c++)
    {

      int index = rand() % cur_hard_unsat_nb;
      sel_c = turb_hardunsat_stack[index];
      while (is_selected_clauses[sel_c] != 0)
      {
        index = (index + 1) % cur_hard_unsat_nb;
        sel_c = turb_hardunsat_stack[index];
      }
      // sel_c = turb_hardunsat_stack[c];
      is_selected_clauses[sel_c] = 1; // 被选择的unsat hard标记为1
      for (lit_small *p = clause_lit_small[sel_c]; (v = p->var_num) != 0; p++)
      {
        if (var_mark[v] == 0)
        {
          count_var_mark++;
          // selected_var[count_var_mark++] = v;
          // limit_var_mark = 100 * (count_var_mark * 1.0 / num_vars);
          // //打上标记的变量不能超过总数的20% if(limit_var_mark > 20)
          // //超过limit就break掉
          if (count_var_mark >= theshold) // wyy-20221213
          {
            flag = 1;
            break;
          }
          var_mark[v] = 1; // 给选择的变量打上标记为1
          selected_var[selected_var_num++] = v;
          // if(cur_soln[v] == 1)  //wyy-20221213 在考虑考虑！
          // 可能是在可满足时候变 if(cur_soln[v] == 1 && rand() % 100 < 50)
          // if(rand() % 100 < 50)
          // if(cur_soln[v] == 1 && hard_unsat_nb <= 10)
          // if(score_small[v] + sscore_small[v] > 0)
          // if(hard_unsat_nb <= 100 && (sscore_small[v] > 0 || cur_soln[v] == 1))
          if (hard_unsat_nb <= 50 && rand() % 100 < 50 && cur_soln[v] == 1)
          {
            turb_flipvar = v;
            flip_small(turb_flipvar); // 将挑选的变量1 -> 0，更新信息
            step_sum++;
          }
        }
      }
      if (flag == 1)
      {
        break;
      }
    }
  }
  else // unsat_small hard < 10 ,剩下的用可满足的硬补
  {
    int unsat_hard_num = cur_hard_unsat_nb;
    int ss = 0;
    // if(hard_unsat_nb == 0) sel_c = rand() % num_hclauses; //wyy-20221214
    for (c = 0; c < 10; c++)
    {
      if (unsat_hard_num > 0)
      {
        sel_c = turb_hardunsat_stack[c];
        is_selected_clauses[sel_c] = 1;
        unsat_hard_num--;
        ss = 1;
      }

      else // 没有不满足的硬子句，选择满足的硬子句，打标记 = 2
      {
        sel_c = rand() % num_hclauses; // wyy-20221214
        while (is_selected_clauses[sel_c] != 0)
        {
          sel_c = (sel_c + 1) % num_hclauses;
        }
        is_selected_clauses[sel_c] = 2;
        ss = 2;
      }

      for (lit_small *p = clause_lit_small[sel_c]; (v = p->var_num) != 0; p++)
      {
        if (var_mark[v] == 0)
        {
          count_var_mark++;
          // selected_var[count_var_mark++] = v;
          // limit_var_mark = 100 * (count_var_mark * 1.0 / num_vars);
          // //打上标记的变量不能超过总数的20% if(limit_var_mark > 20)
          // //超过limit就break掉
          if (count_var_mark >= theshold) // wyy-20221213
          {
            flag = 1;
            break;
          }
          var_mark[v] = 1; // 给选择的变量打上标记为1
          selected_var[selected_var_num++] = v;
          // if(cur_soln[v] == 1 && ss == 1)//wyy-20221213 在考虑考虑！
          // if(cur_soln[v] == 1 && rand() % 100 < 50)//wyy-20221213
          // 在考虑考虑！ if(rand() % 100 < 50 && ss == 2) if((rand() % 100 < 50
          // && ss == 1) || (rand() % 100 < 1 && ss == 2)) if((cur_soln[v] == 1
          // && ss == 1) || (cur_soln[v] == 1 && rand() % 100 < 50 && ss == 2))
          // if(cur_soln[v] == 1 && hard_unsat_nb <= 10)
          // if(hard_unsat_nb <= 100 && (sscore_small[v] > 0 || (ss == 1 &&
          // cur_soln[v] == 1) || (ss == 2 && c <= 2 && cur_soln[v] == 1)))
          //|| (ss == 2 && hard_unsat_nb <= 5))
          // if(ss == 1)
          if (hard_unsat_nb <= 50 && ss == 1 && rand() % 100 < 50 &&
              cur_soln[v] == 1) // && ((ss == 1 && cur_soln[v] == 1) || (ss == 2
                                // && cur_soln[v] == 1)))
          {
            turb_flipvar = v;
            flip_small(turb_flipvar); // 将挑选的变量1 -> 0，更新信息
            step_sum++;
          }
        }
      }
      if (flag == 1)
      {
        break;
      }
    }
  }
  // cout<<z<<endl;
  //  for(c = 0; c < cur_hard_unsat_nb; c++)
  //  {
  //  	cout<<is_selected_clauses[c]<<" ";
  //  }
  /*扰动翻转*/
  // printf("count_var_mark =%d, theshold = %d,
  // hard_unsat_nb=%d\n",count_var_mark,theshold,hard_unsat_nb);
  int turb_step;
  int turb_hardunsat_nb = hard_unsat_nb; // 记录当前不可满足的硬子句个数
  long long turb_opt_unsat_weight;
  int mark_soln = 0;

  int ttt = 0;
  int turb_best_var;
  for (turb_step = 1; turb_step <= 50;
       turb_step++) // wyy-20221213  不用设置那么多 100就够用
  {
    ttt++;

    if (ttt == 1)
      turb_best_var = turb_pick_var_small(-1);
    else
      turb_best_var = turb_pick_var_small(turb_best_var);
    flip_small(turb_best_var);
    if (hard_unsat_nb < turb_hardunsat_nb)
    {
      turb_hardunsat_nb =
          hard_unsat_nb; // 可以一直保证不满足的硬一直减少才更新局部最优解
      turb_opt_unsat_weight = soft_unsat_weight_small;
      mark_soln = 1;
      turb_step = 1;

      // for (v = 1; v <= num_vars; ++v)
      //	turb_best_soln[v] = cur_soln[v];
    }
    if (hard_unsat_nb == 0 &&
        (soft_unsat_weight_small < opt_unsat_weight_small || best_soln_feasible == 0))
    // if (hard_unsat_nb == 0)//unsat_small hard都满足
    {
      break;
    }
  }
  // printf("total step = %d\n",ttt);
  if (mark_soln == 1)
  {
    // soft_unsat_weight_small = turb_opt_unsat_weight;
    // for (v = 1; v <= num_vars; ++v)
    //{
    //	cur_soln[v] = turb_best_soln[v];
    // }
    // init_turb_small();
    ;
  }
}

void Satlike::init_turb_small()
{
  int v, c;
  int j, i;

  // local_soln_feasible = 0;
  // local_opt_unsat_weight = top_clause_weight_small + 1;
  // large_weight_clauses_count = 0;
  // soft_large_weight_clauses_count = 0;

  // ave_soft_weight_small = total_soft_weight_small / num_sclauses;
  // ave_hard_weight_small = 0;
  // inc_hard_weight_small = 0;
  // cout << "ave soft weight is " << ave_soft_weight_small << endl;
  // Initialize clause information
  // for (c = 0; c < num_clauses; c++)
  // {
  // 	clause_visied_times[c] = 0;
  // 	clause_selected_count[c] = 0;

  // 	if (org_clause_weight_small[c] == top_clause_weight_small)
  // 	{
  // 		//clause_weight_small[c] = clause_true_lit_thres_small[c];
  // 		org_unit_weight_small[c] = 1;
  // 		unit_weight_small[c] = org_unit_weight_small[c];
  // 		long long total_sum = 0;
  // 		for (int i = 0; i < clause_lit_count[c]; ++i)
  // 		{
  // 			total_sum += clause_lit_small[c][i].weight;
  // 		}
  // 		clause_weight_small[c] = total_sum / clause_lit_count[c];
  // 		ave_hard_weight_small += clause_weight_small[c];
  // 		clause_total_sum_small[c] = total_sum;//硬子句系数之和
  // 	}
  // 	else
  // 	{
  // 		clause_weight_small[c] = org_clause_weight_small[c];
  // 		clause_total_sum_small[c] = org_clause_weight_small[c];//软子句系数之和
  // 		org_unit_weight_small[c] = ceil((double)clause_weight_small[c] /
  // (double)clause_true_lit_thres_small[c]); 		unit_weight_small[c] = org_unit_weight_small[c];
  // 	}
  /********min{k + amax, asum}**********/
  // if(clause_true_lit_thres_small[c] + clause_max_weight_small[c] <= clause_total_sum_small[c])
  //  {
  //       gap1_small[c] = clause_true_lit_thres_small[c] + clause_max_weight_small[c];
  //    }else
  //        gap1_small[c] = clause_total_sum_small[c];
  /********min{k + amax, asum}**********/
  //}
  // inc_hard_weight_small = ave_hard_weight_small % num_hclauses;
  // ave_hard_weight_small /= num_hclauses;
  // inc_hard_weight_small += ave_soft_weight_small;

  // init_small solution
  //  if (init_solution.size() == 0)
  //  {
  //  	for (v = 1; v <= num_vars; v++)
  //  	{
  //  		cur_soln[v] = 0;
  //  		time_stamp[v] = 0;
  //  		unsat_app_count[v] = 0;
  //  	}
  //  }
  //  else
  //  {
  //  	for (v = 1; v <= num_vars; v++)
  //  	{
  //  		cur_soln[v] = init_solution[v];
  //  		if (cur_soln[v] == 2)
  //  			cur_soln[v] = rand() % 2;
  //  		time_stamp[v] = 0;
  //  		unsat_app_count[v] = 0;
  //  	}
  //  }

  // init_small stacks
  hard_unsat_nb = 0;
  // soft_unsat_nb = 0;//turb_small
  hardunsat_stack_fill_pointer = 0;
  softunsat_stack_fill_pointer = 0;
  unsatvar_stack_fill_pointer = 0;

  /* figure out sat_count_small, sat_var, soft_unsat_weight_small and init_small unsat_stack */
  soft_unsat_weight_small = 0;
  hard_unsat_weight_small = 0;

  for (c = 0; c < num_clauses; ++c)
  {
    sat_count_small[c] = 0;
    for (j = 0; j < clause_lit_count[c]; ++j)
    {

      if (cur_soln[clause_lit_small[c][j].var_num] == clause_lit_small[c][j].sense)
      {
        sat_count_small[c] += clause_lit_small[c][j].weight;
        // sat_var[c] = clause_lit_small[c][j].var_num;
      }
    }
    if (sat_count_small[c] < clause_true_lit_thres_small[c])
    {
      if (org_clause_weight_small[c] != top_clause_weight_small)
        soft_unsat_weight_small +=
            (clause_true_lit_thres_small[c] - sat_count_small[c]) * org_unit_weight_small[c];
      else
        hard_unsat_weight_small += clause_true_lit_thres_small[c] - sat_count_small[c]; // zyj
      unsat_small(c);
    }
    // cout<<"soft_unsat_weight_small "<<soft_unsat_weight_small<<endl;
  }

  /*figure out score_small*/
  int sense;
  long long weight;

  for (v = 1; v <= num_vars; v++)
  {
    score_small[v] = 0;
    sscore_small[v] = 0;
    hhscore_small[v] = 0; // 初始化hhscore
    for (int i = 0; i < var_lit_count[v]; ++i)
    {
      c = var_lit_small[v][i].clause_num;
      sense = var_lit_small[v][i].sense;
      weight = var_lit_small[v][i].weight;
      if (org_clause_weight_small[c] == top_clause_weight_small) // 加入了hhscore
      {
        if (sat_count_small[c] < clause_true_lit_thres_small[c])
        {
          if (sense != cur_soln[v]) // 当约束不满足时，可以直接加入hhscore
          {
            score_small[v] +=
                double(tuned_degree_unit_weight_small[c] *
                       min(clause_true_lit_thres_small[c] - sat_count_small[c], weight));
            // hhscore_small[v] += unit_weight_small[c] * max(weight -
            // (clause_true_lit_thres_small[c] - sat_count_small[c]), 0);
            hhscore_small[v] +=
                1 *
                max(weight - (clause_true_lit_thres_small[c] - sat_count_small[c]), 0LL);
          }
          else
          {
            score_small[v] -= double(tuned_degree_unit_weight_small[c] * weight);
            hhscore_small[v] += 0;
          }
        }
        else if (sat_count_small[c] >= clause_true_lit_thres_small[c])
        {
          if (sat_count_small[c] <= gap1_small[c])
          {
            if (sense == cur_soln[v])
            {
              score_small[v] -= double(
                  tuned_degree_unit_weight_small[c] *
                  max(0LL, clause_true_lit_thres_small[c] - sat_count_small[c] + weight));
              // hhscore_small[v] -= unit_weight_small[c] * min(weight, sat_count_small[c] -
              // clause_true_lit_thres_small[c]);
              hhscore_small[v] -=
                  1 * min(weight, sat_count_small[c] - clause_true_lit_thres_small[c]);
            }
            else
            {
              // hhscore_small[v] += unit_weight_small[c] * min(weight, gap1_small[c] -
              // sat_count_small[c]);
              hhscore_small[v] += 1 * min(weight, gap1_small[c] - sat_count_small[c]);
            }
          }
          else if (sat_count_small[c] > gap1_small[c])
          {
            if (sense == cur_soln[v])
            {
              score_small[v] -= double(
                  tuned_degree_unit_weight_small[c] *
                  max(0LL, clause_true_lit_thres_small[c] - sat_count_small[c] + weight));
              // hhscore_small[v] -= unit_weight_small[c] * max(weight - (sat_count_small[c] -
              // gap1_small[c]), 0);
              hhscore_small[v] -= 1 * max(weight - (sat_count_small[c] - gap1_small[c]), 0LL);
            }
          }
        }
      }
      else
      {
        if (sat_count_small[c] < clause_true_lit_thres_small[c])
        {
          if (sense != cur_soln[v])
          {
            sscore_small[v] += unit_weight_small[c] * tune_soft_clause_weight_small[c];
          }
          else
            sscore_small[v] -= unit_weight_small[c] * tune_soft_clause_weight_small[c];
        }
        else if (sat_count_small[c] >= clause_true_lit_thres_small[c])
        {
          if (sense == cur_soln[v])
          {
            sscore_small[v] -= unit_weight_small[c] * tune_soft_clause_weight_small[c];
          }
        }
      }
    }
  }

  // init_small goodvars stack
  goodvar_stack_fill_pointer = 0;

  for (v = 1; v <= num_vars; v++)
  {
    // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v] > 0)//加入hhscore
    if (score_small[v] + sscore_small[v] > 0)
    {
      already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
      mypush(v, goodvar_stack);
    }
    else
      already_in_goodvar_stack[v] = -1;
  }
}

int Satlike::turb_pick_var_small(int last_flip_var) // 轮盘转法
{
  int turb_best_var;
  int i, v;
  long long pick_score[300] = {0};
  int pos_score_var[300] = {0}; // 记录挑选变量的v的位置
  // long long *pick_score = new long long[30]();
  // int *pos_score_var = new int[30]();
  int bms_turb_pick;
  long long abs_min_pick_score, abs_min;
  int turb_size = 1;
  int pos_size = 1;
  long long min_pick_score = 200000000000000; // 最大的分数是多少
  long long turb_seed;
  long long sum_pick_score;
  long long ssscore;
  // if(selected_var_num <= 200)   //20 50
  //{
  bms_turb_pick = selected_var_num / 2 + 1;
  //}else
  //	bms_turb_pick = 100;     //bms

  turb_best_var = selected_var[rand() % selected_var_num];
  // turb_best_var = selected_var[0];
  // if(last_flip_var == turb_best_var) turb_best_var = selected_var[1];
  for (i = 1; i < bms_turb_pick; i++) // 看看<20，要不要单独写
  {
    v = selected_var[rand() % selected_var_num];

    // v = selected_var[i];
    if (last_flip_var == v)
      continue;
    // v = i;
    if (score_small[v] + sscore_small[v] > score_small[turb_best_var] + sscore_small[turb_best_var])
      turb_best_var = v;
    else if (score_small[v] + sscore_small[v] ==
             score_small[turb_best_var] + sscore_small[turb_best_var])
    {
      if (hhscore_small[v] > hhscore_small[turb_best_var])
      {
        turb_best_var = v;
      }
      else if (hhscore_small[v] == hhscore_small[turb_best_var])
      {
        int rand_select = rand() % 2;
        if (rand_select == 1)
        {
          turb_best_var = v;
        }
      }
    }
  }
  return turb_best_var;

  for (i = 0; i < bms_turb_pick; i++) // 看看<20，要不要单独写
  {
    v = selected_var[rand() % selected_var_num]; // 会重复，没去重
    ssscore = score_small[v] + sscore_small[v];
    pick_score[turb_size++] = ssscore; // pick_score从1开始
    pos_score_var[pos_size++] = v;     // v 和 v 的score保持一致
    if (ssscore < min_pick_score)
    {
      min_pick_score = ssscore; // 记录选择的变量中分数最小的
    }
  }
  /* wyy20221213
  for(i = 1; i <= bms_turb_pick; i++)
  {
          if(min_pick_score <= 0)
          {
                  abs_min = abs(min_pick_score);//如果最小值<0，分数 + abs+1
                  abs_min_pick_score = abs_min + 1;
                  //cout<<min_pick_score<<" "<<abs_min<<"
  "<<abs_min_pick_score<<endl; pick_score[i] = pick_score[i-1] + pick_score[i] +
  abs_min_pick_score;  //直接在原数组上改了 sum_pick_score =
  pick_score[bms_turb_pick];  //最后的是分数总和，用来取随机数的范围
          }
          else  //最小的分数>=0，不用+abs
          {
                  pick_score[i] = pick_score[i-1] + pick_score[i];
                  sum_pick_score = pick_score[bms_turb_pick];
  //最后的是分数总和，用来取随机数的范围
          }
  }

  */
  // wyy 20221212  ---begin
  if (min_pick_score <= 0)
  {
    abs_min = abs(min_pick_score); // 如果最小值<0，分数 + abs+1
    abs_min_pick_score = abs_min + 1;
    // pick_score[0] +=  abs_min_pick_score;
    for (i = 1; i <= bms_turb_pick; i++)
    { // wyy 20221212  没有等于！
      pick_score[i] = pick_score[i] + abs_min_pick_score +
                      pick_score[i - 1]; // 直接在原数组上改了
    }
  }
  else
  {
    for (i = 1; i <= bms_turb_pick; i++)
    { // wyy 20221212
      pick_score[i] = pick_score[i] + pick_score[i - 1];
    }
  }
  sum_pick_score = pick_score[bms_turb_pick];
  // wyy 20221212  ---end
  turb_seed = rand() % sum_pick_score; // 取随机数
  for (i = 1; i <= bms_turb_pick; i++) // wyy 20221212
  {
    if (turb_seed < pick_score[i])
    {
      turb_best_var = pos_score_var[i]; // 找到对应的var
      break;
    }
  }
  return turb_best_var;
}

// void Satlike::get_obj(string opb_file_name)
// {
// 	ifstream opb_ifile(opb_file_name.c_str());
// 	int num_hardclauses, i;
// 	istringstream ss;
// 	istringstream ss2;

// 	string line, coeff, var, other;
// 	getline(opb_ifile, line);

// 	ss.clear();			   // 多次使用stringstream，需要清空
// 	ss.str(line);		   // 把line中的字符串存入字符串流中
// 	ss.seekg(0, ios::beg); // seekg(offset,
// place)设置输入文件流的文件流指针位置，ios::beg文件的开始位置 	ss >> other;
// // 过滤掉 * 	ss >> other;		   // 过滤掉 #variable= 	ss >>
// num_vars_opb;	   // 获取变量数 	ss >> other;		   // 过滤掉
// #constraint= 	ss >> num_hardclauses;

// 	// int m = 0;
// 	int v;
// 	// opb = new int[num_vars_opb + 10];
// 	for (v = 1; v <= num_vars_opb; v++)
// 	{
// 		opb[v] = 0;
// 	}

// 	getline(opb_ifile, line);
// 	while (line[0] == '*')
// 	{
// 		getline(opb_ifile, line);
// 	}

// 	ss.clear();
// 	ss.str(line);
// 	ss.seekg(0, ios::beg);
// 	ss >> coeff;
// 	ss >> coeff >> var;
// 	long long icoeff, ivar;
// 	while (coeff != ";")
// 	{
// 		ss2.clear();
// 		ss2.str(coeff); //+1
// 		ss2.seekg(0, ios::beg);
// 		ss2 >> icoeff; //+1
// 					   // opb[m++] = icoeff;
// 		ss2.clear();
// 		ss2.str(var.substr(1));
// 		ss2.seekg(0, ios::beg);
// 		ss2 >> ivar; // 1
// 		// opb[m++] = icoeff;
// 		opb[ivar] = icoeff;

// 		ss >> coeff >> var; // coeff：+2，var：x2
// 	}
// 	if (num_vars == num_vars_opb)
// 	{
// 		for (i = 1; i <= num_vars; i++)
// 		{
// 			obj_300 += best_soln_300[i] * opb[i];
// 			obj_1800 += best_soln_1800[i] * opb[i];
// 			obj_3600 += best_soln[i] * opb[i];
// 		}
// 	}
// 	else
// 	{
// 		cout << " error :num_vars != num_vars_opb "
// 			 << " " << opb_file_name << endl;
// 		cout << "num_vars = " << num_vars << "num_vars_opb = " <<
// num_vars_opb << endl;
// 	}
// }

void Satlike::check_softunsat_weight_small()
{
  int c, j, flag;
  long long verify_unsat_weight = 0;

  for (c = 0; c < num_clauses; ++c)
  {
    flag = 0;
    long long tem_clause_true_lit_count = 0;
    for (j = 0; j < clause_lit_count[c]; ++j)
    {
      if (cur_soln[clause_lit_small[c][j].var_num] == clause_lit_small[c][j].sense)
      {
        tem_clause_true_lit_count++;
      }
    }
    if (tem_clause_true_lit_count >= clause_true_lit_thres_small[c])
      flag = 1;

    if (flag == 0)
    {
      if (org_clause_weight_small[c] == top_clause_weight_small) // verify hard clauses
      {
        continue;
      }
      else
      {
        verify_unsat_weight += org_unit_weight_small[c] * (clause_true_lit_thres_small[c] -
                                                           tem_clause_true_lit_count);
      }
    }
  }

  if (verify_unsat_weight != soft_unsat_weight_small)
  {
    cout << step << endl;
    cout << "verify unsat_small weight is" << verify_unsat_weight
         << " and soft unsat_small weight is " << soft_unsat_weight_small << endl;
  }
  // return 0;
}

bool Satlike::verify_sol_small()
{
  int c, j;

  for (c = 0; c < num_clauses; ++c)
  {
    if (org_clause_weight_small[c] == top_clause_weight_small)
    {
      long long tem_clause_true_lit_count = 0;
      for (j = 0; j < clause_lit_count[c]; ++j)
      {
        if (best_soln[clause_lit_small[c][j].var_num] == clause_lit_small[c][j].sense)
        {
          tem_clause_true_lit_count += clause_lit_small[c][j].weight;
        }
      }
      if (tem_clause_true_lit_count < clause_true_lit_thres_small[c])
        return false;
    }
  }
  return true;
}

void Satlike::simple_print_small()
{
  if (best_soln_feasible == 1)
  {
    if (verify_sol_small() == 1)
      cout << opt_unsat_weight_small << '\t' << opt_time << endl;
    else
      cout << "solution is wrong " << endl;
  }
  else
    cout << -1 << '\t' << -1 << endl;
}

void Satlike::increase_weights_small()
{
  int i, c, v;
  long long weight;

  int flag = 0;
  // long long inc_hard_weight_small;
  for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
  {
    c = hardunsat_stack[i];
    if (clause_visied_times[c] < clause_true_lit_thres_small[c] / clause_weight_small[c])
    {
      clause_visied_times[c]++;
      continue;
    }
    else
    {
      clause_visied_times[c] = 0;
    }

    inc_hard_weight_small += clause_weight_small[c];
    // clause_weight_small[c] += (h_inc * clause_true_lit_thres_small[c]);
    // cout << "c: " << c << endl;
    unit_weight_small[c] += h_inc;
    tuned_degree_unit_weight_small[c] =
        double(unit_weight_small[c]) / avg_clause_coe_small[c]; // Nupbo

    for (lit_small *p = clause_lit_small[c]; (v = p->var_num) != 0; p++)
    {
      weight = p->weight;
      if (p->sense != cur_soln[v])
      {
        score_small[v] += double(h_inc * min(clause_true_lit_thres_small[c] - sat_count_small[c],
                                             weight)) /
                          avg_clause_coe_small[c];
        if (score_small[v] + sscore_small[v] > 0 && already_in_goodvar_stack[v] == -1)
        // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v] > 0 &&
        // already_in_goodvar_stack[v] == -1)
        {
          already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
          mypush(v, goodvar_stack);
        }
      }
      else
      {
        score_small[v] -= double(h_inc * weight) / avg_clause_coe_small[c];
        if (already_in_goodvar_stack[v] != -1 && score_small[v] + sscore_small[v] <= 0)
        // if (already_in_goodvar_stack[v] != -1 && score_small[v] + sscore_small[v] + ans *
        // hhscore_small[v] <= 0)
        {
          int top_v = mypop(goodvar_stack);
          goodvar_stack[already_in_goodvar_stack[v]] = top_v;
          already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
          already_in_goodvar_stack[v] = -1;
        }
      }
    }
  }

  // cout << "now ave hard weight is " << ave_hard_weight_small << endl; &&
  // ave_soft_weight_small - ave_hard_weight_small > 400 if (soft_unsat_weight_small >=
  // opt_unsat_weight_small && ave_soft_weight_small - ave_hard_weight_small < 100)
  if (0 == hard_unsat_nb)
  {
    // flag = 1;
    ave_soft_weight_small += total_soft_weight_small / num_sclauses;
    inc_hard_weight_small += total_soft_weight_small / num_sclauses;
    for (c = 0; c < num_clauses; ++c)
    {
      if (org_clause_weight_small[c] == top_clause_weight_small)
        continue;

      // unit_weight_small[c] += org_unit_weight_small[c];
      unit_weight_small[c] += 1; // Nupbo

      if (sat_count_small[c] < clause_true_lit_thres_small[c])
      {
        for (lit_small *p = clause_lit_small[c]; (v = p->var_num) != 0; p++)
        {
          sscore_small[v] += tune_soft_clause_weight_small[c];
          // min(clause_true_lit_thres_small[c] - sat_count_small[c], weight);
          if (score_small[v] + sscore_small[v] > 0 && already_in_goodvar_stack[v] == -1)
          // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v]> 0 &&
          // already_in_goodvar_stack[v] == -1)
          {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v, goodvar_stack);
          }
        }
      }
      else if (sat_count_small[c] == 1)
      {
        for (lit_small *p = clause_lit_small[c]; (v = p->var_num) != 0; p++)
        {
          // weight = p->weight;
          // sscore_small[v] += org_unit_weight_small[c];
          if (p->sense == cur_soln[v])
          {
            sscore_small[v] -= tune_soft_clause_weight_small[c];
            if (already_in_goodvar_stack[v] != -1 && score_small[v] + sscore_small[v] <= 0)
            // if (already_in_goodvar_stack[v] != -1 && score_small[v] + sscore_small[v] +
            // ans * hhscore_small[v]<= 0)
            {
              int top_v = mypop(goodvar_stack);
              goodvar_stack[already_in_goodvar_stack[v]] = top_v;
              already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
              already_in_goodvar_stack[v] = -1;
            }
          }
        }
      }
    }
  }

  ave_hard_weight_small += (inc_hard_weight_small / num_hclauses);
  inc_hard_weight_small %= num_hclauses;
}

void Satlike::smooth_weights_small()
{
  int i, clause, v;
  long long weight;
  if (soft_unsat_weight_small < opt_unsat_weight_small &&
      ave_soft_weight_small > (total_soft_weight_small / num_sclauses))
  {
    ave_soft_weight_small -= (total_soft_weight_small / num_sclauses);
    inc_hard_weight_small -= (total_soft_weight_small / num_sclauses);
    if (inc_hard_weight_small < 0)
      inc_hard_weight_small = 0;
    for (int c = 0; c < num_clauses; ++c)
    {
      if (org_clause_weight_small[c] == top_clause_weight_small)
      {
        if (unit_weight_small[c] == 1 && sat_count_small[c] < clause_true_lit_thres_small[c])
          continue;

        unit_weight_small[c]--;
        for (lit_small *p = clause_lit_small[c]; (v = p->var_num) != 0; p++)
        {
          weight = p->weight;
          if (p->sense == cur_soln[v])
          {
            if (sat_count_small[c] - weight < clause_true_lit_thres_small[c])
            {
              score_small[v] += clause_true_lit_thres_small[c] - sat_count_small[c] + weight;
              if (score_small[v] + sscore_small[v] > 0 && already_in_goodvar_stack[v] == -1)
              // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v] > 0 &&
              // already_in_goodvar_stack[v] == -1)
              {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
              }
            }
          }
        }
      }
      else
      {
        unit_weight_small[c]--;
        for (lit_small *p = clause_lit_small[c]; (v = p->var_num) != 0; p++)
        {
          weight = p->weight;
          if (p->sense == cur_soln[v])
          {
            if (sat_count_small[c] - weight < clause_true_lit_thres_small[c])
            {
              sscore_small[v] += clause_true_lit_thres_small[c] - sat_count_small[c] + weight;
              if (score_small[v] + sscore_small[v] > 0 && already_in_goodvar_stack[v] == -1)
              // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v] > 0 &&
              // already_in_goodvar_stack[v] == -1)
              {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
              }
            }
          }
        }
      }
    }
  }
  else
  {
    for (int c = 0; c < num_clauses; ++c)
    {
      if (org_clause_weight_small[c] == top_clause_weight_small)
      {
        if (unit_weight_small[c] == 1 && sat_count_small[c] < clause_true_lit_thres_small[c])
          continue;

        unit_weight_small[c]--;
        for (lit_small *p = clause_lit_small[c]; (v = p->var_num) != 0; p++)
        {
          weight = p->weight;
          if (p->sense == cur_soln[v])
          {
            if (sat_count_small[c] - weight < clause_true_lit_thres_small[c])
            {
              score_small[v] += clause_true_lit_thres_small[c] - sat_count_small[c] + weight;
              if (score_small[v] + sscore_small[v] > 0 && already_in_goodvar_stack[v] == -1)
              // if (score_small[v] + sscore_small[v] + ans * hhscore_small[v] > 0 &&
              // already_in_goodvar_stack[v] == -1)
              {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
              }
            }
          }
        }
      }
    }
  }
}

void Satlike::update_clause_weights_small()
{
  /*
  if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability)
  {
          smooth_weights();
  }
  else
  {*/
  increase_weights_small();
  //}
}

inline void Satlike::unsat_small(int clause)
{
  if (org_clause_weight_small[clause] == top_clause_weight_small)
  {
    index_in_hardunsat_stack[clause] = hardunsat_stack_fill_pointer;
    mypush(clause, hardunsat_stack);
    hard_unsat_nb++;
  }
  else
  {
    index_in_softunsat_stack[clause] = softunsat_stack_fill_pointer;
    mypush(clause, softunsat_stack);
    // soft_unsat_weight_small += org_clause_weight_small[clause];
  }
}

inline void Satlike::sat_small(int clause)
{
  int index, last_unsat_clause;

  if (org_clause_weight_small[clause] == top_clause_weight_small)
  {

    last_unsat_clause = mypop(hardunsat_stack);
    index = index_in_hardunsat_stack[clause];
    hardunsat_stack[index] = last_unsat_clause;
    index_in_hardunsat_stack[last_unsat_clause] = index;

    hard_unsat_nb--;
  }
  else
  {
    last_unsat_clause = mypop(softunsat_stack);
    index = index_in_softunsat_stack[clause];
    softunsat_stack[index] = last_unsat_clause;
    index_in_softunsat_stack[last_unsat_clause] = index;

    // soft_unsat_weight_small -= org_clause_weight_small[clause];
  }
}

void Satlike::check_new_score_small()
{
  long long tem_score = 0;
  long long tem_sscore = 0;
  int sense, c, v, i;
  long long weight;
  for (v = 1; v <= num_vars; v++)
  {
    tem_score = 0;
    tem_sscore = 0;
    for (i = 0; i < var_lit_count[v]; ++i)
    {
      c = var_lit_small[v][i].clause_num;
      sense = var_lit_small[v][i].sense;
      weight = var_lit_small[v][i].weight;
      if (org_clause_weight_small[c] == top_clause_weight_small)
      {
        if (sat_count_small[c] < clause_true_lit_thres_small[c])
        {
          if (sense != cur_soln[v])
          {
            tem_score += unit_weight_small[c] *
                         min(clause_true_lit_thres_small[c] - sat_count_small[c], weight);
          }
          else
            tem_score -= unit_weight_small[c] * weight;
        }
        else if (sat_count_small[c] >= clause_true_lit_thres_small[c])
        {
          if (sense == cur_soln[v])
          {
            tem_score -= unit_weight_small[c] * max(0LL, clause_true_lit_thres_small[c] -
                                                             sat_count_small[c] + weight);
          }
        }
      }
      else
      {
        if (sat_count_small[c] < clause_true_lit_thres_small[c])
        {
          if (sense != cur_soln[v])
          {
            tem_sscore += unit_weight_small[c] *
                          min(clause_true_lit_thres_small[c] - sat_count_small[c], weight);
          }
          else
            tem_sscore -= unit_weight_small[c] * weight;
        }
        else if (sat_count_small[c] >= clause_true_lit_thres_small[c])
        {
          if (sense == cur_soln[v])
          {
            tem_sscore -= unit_weight_small[c] * max(0LL, clause_true_lit_thres_small[c] -
                                                              sat_count_small[c] + weight);
          }
        }
      }
    }
    if (tem_score != score_small[v] || tem_sscore != sscore_small[v])
    {

      cout << "score_small is worng in variable " << v << endl;
      cout << "tem_score is " << tem_score << endl;
      cout << "score_small function is " << score_small[v] << endl;
      cout << "flip_small num is " << step << endl;

      for (i = 0; i < var_lit_count[v]; ++i)
      {
        c = var_lit_small[v][i].clause_num;
        sense = var_lit_small[v][i].sense;
        weight = var_lit_small[v][i].weight;
        cout << c << " ";
      }
      cout << endl;
      exit(0);
      break;
    }
  }

  long long tem_unsat_softweight = 0;
  for (int i = 0; i < num_clauses; ++i)
  {
    if (org_clause_weight_small[i] == top_clause_weight_small)
      continue;
    if (sat_count_small[i] < clause_true_lit_thres_small[i])
    {
      tem_unsat_softweight += (clause_true_lit_thres_small[i] - sat_count_small[i]);
    }
  }
  if (tem_unsat_softweight != soft_unsat_weight_small)
  {
    cout << "verify softunsat weight wrong " << endl;
    exit(0);
  }
}

#ifdef USEPRESOLVE
std::pair<std::string, std::string> split(std::string str)
{
  std::vector<std::string> internal;
  std::stringstream ss(str); // Turn the string into a stream.
  std::string tok;

  while (getline(ss, tok, ' '))
  {
    internal.push_back(tok);
  }

  return std::pair<std::string, std::string>(internal[0],
                                             internal[internal.size() - 1]);
}

namespace utils
{

  template <typename Enumeration>
  auto as_integer(Enumeration const value)
      -> typename std::underlying_type<Enumeration>::type
  {
    return static_cast<typename std::underlying_type<Enumeration>::type>(value);
  }

  template <typename T>
  void print_problem(papilo::Problem<T> prob)
  {
    const papilo::ConstraintMatrix<T> &consmatrix = prob.getConstraintMatrix();
    const papilo::Vec<std::string> &consnames = prob.getConstraintNames();
    const papilo::Vec<std::string> &varnames = prob.getVariableNames();
    const papilo::Vec<T> &lhs = consmatrix.getLeftHandSides();
    const papilo::Vec<T> &rhs = consmatrix.getRightHandSides();
    const papilo::Objective<T> &obj = prob.getObjective();
    const papilo::Vec<papilo::ColFlags> &col_flags = prob.getColFlags();
    const papilo::Vec<papilo::RowFlags> &row_flags = prob.getRowFlags();

    std::cout << "Print Problem: " << prob.getName() << std::endl;

    std::cout << "n vars: " << consmatrix.getNCols() << std::endl;
    std::cout << "m constraints: " << consmatrix.getNRows() << std::endl;
    std::cout << "Variable Names: " << std::endl;

    std::cout << "  ";
    for (papilo::String varname : varnames)
    {
      std::cout << varname << ", ";
    }
    std::cout << std::endl;

    const auto cols = *consmatrix.getColumns();

    const auto getRowZeroCoeff = consmatrix.getRowCoefficients(0);
    const auto len = getRowZeroCoeff.getLength();

    const T *rowZeroCoeffVal = getRowZeroCoeff.getValues();
    for (int i = 0; i < len; ++i)
    {
      const auto test = int(rowZeroCoeffVal[i]);
    }

    std::cout << "Constraint matrix:" << std::endl;
    for (int i = 0; i < consmatrix.getNRows(); ++i)
    {
      const papilo::SparseVectorView<T> row = consmatrix.getRowCoefficients(i);
      const T *rowVals = row.getValues();
      const int *indices = row.getIndices();
      const auto len = row.getLength();

      for (int j = 0; j < len; ++j)
      {
        std::cout << std::setw(7) << varnames[indices[j]] << ":" << int(rowVals[j]);
      }
      std::cout << std::endl;
    }
  }
  template <typename T>
  void printVector(papilo::Vec<T> const &input)
  {
    for (int i = 0; i < input.size(); i++)
    {
      std::cout << input.at(i) << ' ';
    }
    std::cout << std::endl;
  }

}

namespace PresolveOpb
{
  template <typename T>
  struct OpbParser
  {
    static papilo::ProblemBuilder<T> parseProbOpb(char *filename)
    {

      std::ifstream file(filename, std::ifstream::in);
      if (file.fail())
      {
        file.close();
        throw "c " + std::string(filename) + " does not exist!";
      }
      // Create Problem builder
      papilo::ProblemBuilder<T> probBuilder;
      probBuilder.setProblemName(filename);

      int nCols;
      int nRows;

      for (int i = 0; i < 9; ++i)
      {
        std::string temp;
        file >> temp;
        if (i == 2)
          nCols = std::stoi(temp);
        if (i == 4)
          nRows = std::stoi(temp);
        if (i == 8)
          if (stoi(temp) > 63)
          {
            printf("s UNSUPPORTED\n");
            exit(0);
          }
      }

      // set dims
      probBuilder.setNumCols(nCols);
      probBuilder.setNumRows(nRows);

      // set all vars to bool
      for (int i = 0; i < probBuilder.getNumCols(); ++i)
      {
        probBuilder.setColUb(i, 1);
        probBuilder.setColLb(i, 0);
        probBuilder.setColIntegral(i, true);
        probBuilder.setColName(i, "x" + std::to_string(i + 1));
      }

      std::string commentLineTemp;
      bool loadingObj = false;
      long long coeff;
      int newcol = 0;

      // Mapping vars to col index
      std::map<std::string, int> varMap;
      std::string s;

      // Get objective function if one is present:
      while (file >> s)
      {
        if (s == "*" || s[0] == '*')
          std::getline(file, commentLineTemp);
        // Load objective function
        else if (s == "min:")
          loadingObj = true, opt_dec_model = false;
        else if (s == ";")
        {
          loadingObj = false;
        }
        else if (loadingObj)
        {
          if (s[0] == '-' || s[0] == '+' || isdigit(s[0]))
            coeff = std::stoll(s);
          else
          {
            auto addr = varMap.find(s);
            if (addr == varMap.end())
            {
              varMap[s] = newcol++;
              addr = varMap.find(s);
              probBuilder.setColName(addr->second, s);
            }
            int col = addr->second;
            probBuilder.setObj(col, (T)coeff);
          }
        }
        // TODO: check why this is necessary.
        else
        {
          file.close();
          file.open(filename, std::ifstream::in);
          break;
        }
      }

      int row = 0;

      while (file >> s)
      {
        // Handle coefficient case
        if (s[0] == '+' || s[0] == '-' || isdigit(s[0]))
          coeff = std::stoll(s);
        // Handle bound
        else if (s == ">=")
        {
          probBuilder.setRowRhsInf(row, true);
          probBuilder.setRowLhsInf(row, false);
          file >> s;
          probBuilder.setRowLhs(row, (T)std::stoll(s));
        }
        // Note: Case not in normal opb files
        else if (s == "<=")
        {
          probBuilder.setRowRhsInf(row, false);
          probBuilder.setRowLhsInf(row, true);
          file >> s;
          probBuilder.setRowLhs(row, (T)std::stoll(s));
        }
        else if (s == "=")
        {
          probBuilder.setRowRhsInf(row, false);
          probBuilder.setRowLhsInf(row, false);
          file >> s;
          probBuilder.setRowLhs(row, (T)std::stoll(s));
          probBuilder.setRowRhs(row, (T)std::stoll(s));
        }
        // Handle var
        else if (s[0] == 'x')
        {
          auto addr = varMap.find(s);
          if (addr == varMap.end())
          {
            varMap[s] = newcol++;
            addr = varMap.find(s);
            probBuilder.setColName(addr->second, s);
          }
          int col = addr->second;
          probBuilder.addEntry(row, col, (T)coeff);
        }
        else if (s == ";")
          ++row;
        // If comment or objective function push iterator past line
        else if (s == "*" || s[0] == '*' || s[0] == 'm')
          std::getline(file, commentLineTemp);
      }

      file.close();
      return probBuilder;
    }
  };

  struct ParamParser
  {
    static std::map<std::string, std::string>
    ParseParamFile(std::string filename)
    {
      std::map<std::string, std::string> paramList;
      std::ifstream file(filename);
      if (file.fail())
      {
        throw "Parameters not found. Path given: " + filename;
      }
      std::string s;

      while (std::getline(file, s))
      {
        if (s.length() < 2 || s[0] == '#')
          continue;
        paramList.insert(split(s));
      }
      return paramList;
    }
  };

} // namespace PresolveOpb

void Satlike::presolve_build(char *filename)
{
  printf("c Use Presolve\n");
  use_presolve = true;
  int i, v, c;
  int num_hc;
  int num_intsize;

  probBuilder = PresolveOpb::OpbParser<double>::parseProbOpb(filename);
  printf("c Parse finsih\n");
  prob = probBuilder.build();
  presolver.addDefaultPresolvers();
  papilo::ParameterSet paramset = presolver.getParameters();
  /*std::map <std::string, std::string> params = PresolveOpb::ParamParser::ParseParamFile("../parameters.opb.txt");
  std::map <std::string, std::string>::iterator itr;

  for (itr = params.begin(); itr != params.end(); ++itr) {
    std::cout << (itr->first).c_str() << " " << (itr->second).c_str() << std::endl;
    paramset.parseParameter((itr->first).c_str(), (itr->second).c_str());
  }
  paramset.parseParameter("parallelrows.enabled", "0");
  paramset.parseParameter("parallelrows.enabled", "0");
  paramset.parseParameter("substitution.binarieswithints", "0");
  paramset.parseParameter("message.verbosity", "0");
  paramset.parseParameter("presolve.threads", "1");*/
  paramset.parseParameter("coefftightening.enabled", "1");
  paramset.parseParameter("colsingleton.enabled", "1");
  paramset.parseParameter("domcol.enabled", "1");
  paramset.parseParameter("doubletoneq.enabled", "1");
  paramset.parseParameter("dualfix.enabled", "1");
  paramset.parseParameter("dualinfer.enabled", "1");
  paramset.parseParameter("fixcontinuous.enabled", "1");
  paramset.parseParameter("implint.enabled", "1");
  paramset.parseParameter("message.verbosity", "0");
  paramset.parseParameter("numerics.epsilon", "1.0000000000000001e-09");
  paramset.parseParameter("numerics.feastol", "9.9999999999999995e-07");
  paramset.parseParameter("numerics.hugeval", "100000000");
  paramset.parseParameter("parallelcols.enabled", "0");
  paramset.parseParameter("parallelrows.enabled", "0");
  paramset.parseParameter("presolve.abortfac", "0.00080000000000000004");
  paramset.parseParameter("presolve.boundrelax", "0");
  paramset.parseParameter("presolve.componentsmaxint", "0");
  paramset.parseParameter("presolve.compressfac", "0.84999999999999998");
  paramset.parseParameter("presolve.detectlindep", "1");
  paramset.parseParameter("presolve.dualreds", "2");
  paramset.parseParameter("presolve.lpabortfac", "0.01");
  paramset.parseParameter("presolve.minabscoeff", "1e-10");
  paramset.parseParameter("presolve.randomseed", "0");
  paramset.parseParameter("presolve.removeslackvars", "1");
  paramset.parseParameter("presolve.threads", "1");
  // paramset.parseParameter("presolve.tlim", "1.7976931348623157e+308");
  // paramset.parseParameter("presolve.tlim", "100");
  // paramset.parseParameter("presolve.tlim", std::to_string(presolveTimeLimit));
  paramset.parseParameter("presolve.weakenlpvarbounds", "0");
  paramset.parseParameter("probing.enabled", "1");
  paramset.parseParameter("probing.maxinitialbadgesize", "1000");
  paramset.parseParameter("probing.minbadgesize", "10");
  paramset.parseParameter("probing.mincontdomred", "0.29999999999999999");
  paramset.parseParameter("propagation.enabled", "1");
  paramset.parseParameter("simpleprobing.enabled", "1");
  paramset.parseParameter("simplifyineq.enabled", "1");
  paramset.parseParameter("sparsify.enabled", "1");
  paramset.parseParameter("sparsify.maxscale", "1000");
  paramset.parseParameter("stuffing.enabled", "1");
  paramset.parseParameter("substitution.binarieswithints", "0");
  paramset.parseParameter("substitution.enabled", "1");
  paramset.parseParameter("substitution.markowitz_tolerance", "0.01");
  paramset.parseParameter("substitution.maxfillin", "10");
  paramset.parseParameter("substitution.maxshiftperrow", "10");

  int PretimeLimit;
  if (cutoff_time > 1800)
  { // 如果运行时间超过1800秒
    PretimeLimit = 200;
  }
  else if (600 < cutoff_time <= 1800)
  {
    PretimeLimit = 100;
  }
  else if (cutoff_time <= 600)
  { // 如果运行时间少于1000秒
    PretimeLimit = 10;
  }
  else
  {
    PretimeLimit = 10; // 默认值或者基于其他逻辑的值
  }
  paramset.parseParameter("presolve.tlim", std::to_string(PretimeLimit).c_str());

  printf("c Start Presolve\n");
  // std::ostringstream oss;
  // std::ostream_iterator<char> out_it(oss);
  // paramset.printParams(out_it);
  // std::cout << oss.str() << std::endl;
  result = presolver.apply(prob);
  opt_time = get_runtime();

  if (utils::as_integer(result.status) > 2)
  {
    use_presolve = false;
    build_instance_small(filename);
    return;
  }
  // printf("%s %g\n", basename(filename), opt_time);
  /*auto varlbounds = prob.getLowerBounds();
  int cnt = 0;
  for(double b : varlbounds) {
    printf("%d %d\n", cnt++, (int)b);
     if ((int)b != 0) throw std::invalid_argument("NOT BOOL! lower bound: " + std::to_string(b));
  }
  cnt = 0;
  auto varubounds = prob.getUpperBounds();
  for(double b : varubounds) {
    printf("%d %d\n", cnt++, (int)b);
     if ((int)b != 1) throw std::invalid_argument("NOT BOOL! upper bound: " + std::to_string(b));
  }

  for(papilo::String name : prob.getVariableNames()) {
     if(name[0] != 'x') throw std::invalid_argument("Incorrect naming of var " + name);
  }*/
  const papilo::ConstraintMatrix<double> &consmatrix =
      prob.getConstraintMatrix();
  const papilo::Vec<std::string> &varnames = prob.getVariableNames();
  const papilo::Vec<double> &lhs = consmatrix.getLeftHandSides();
  const papilo::Vec<papilo::RowFlags> &row_flags = prob.getRowFlags();
  const papilo::Vec<double> &rhs = consmatrix.getRightHandSides();

  // std::cout << "* #variable= " << consmatrix.getNCols() << " #constraint= " << consmatrix.getNRows() << std::endl;

  num_vars = consmatrix.getNCols();
  num_hclauses = consmatrix.getNRows();

  for (int i = 0; i < consmatrix.getNRows(); ++i)
  {
    int signBit = 1;
    if (!row_flags[i].test(papilo::RowFlag::kRhsInf) &&
        !row_flags[i].test(papilo::RowFlag::kLhsInf))
    {
      ++num_hclauses;
    }
    /*if (!row_flags[i].test( papilo::RowFlag::kRhsInf) && !row_flags[i].test(papilo::RowFlag::kLhsInf)) {
    std::cout << "=\n";
}
else if (row_flags[i].test(papilo::RowFlag::kRhsInf) || row_flags[i].test(papilo::RowFlag::kLhsInf)) {
    std::cout << ">=\n";
}
else {
    throw std::invalid_argument( "Row " + std::to_string(i) + " contains invalid constraint. LhsInf: " + std::to_string(row_flags[i].test( papilo::RowFlag::kLhsInf))
                                                                                         + " RhsInf: " + std::to_string(row_flags[i].test( papilo::RowFlag::kRhsInf)));
}*/
  }
  top_clause_weight_small = 0;
  const papilo::Objective<double> objective = prob.getObjective();
  num_sclauses = 0;
  for (int i = 0; i < objective.coefficients.size(); ++i)
  {
    if (objective.coefficients[i] == 0)
      continue;
    if (objective.coefficients[i] < 0)
    {
      top_clause_weight_small +=
          -(long long)objective.coefficients[i]; // top_clause_weight_small = 0 - (-1)
      sumneg_min_small += -(long long)objective.coefficients[i];
    }
    else if (objective.coefficients[i] > 0)
      top_clause_weight_small += (long long)objective.coefficients[i];
    if (top_clause_weight_small < 0)
    {
      use_presolve = false;
      printf("c -top-nopre\n");
      build_instance_small(filename);
      return;
    }
    ++num_sclauses;
  }
  top_clause_weight_small = top_clause_weight_small + 1;
  num_clauses = num_hclauses + num_sclauses;
  printf("c After Reduce Vars: %d Clauses: %d Top clause weight: %lld Hard Clauses: %d\n", num_vars, num_clauses, top_clause_weight_small, num_hclauses);
  allocate_memory_small();
  for (c = 0; c < num_clauses; c++)
  {
    clause_lit_count[c] = 0;
    clause_true_lit_thres_small[c] = 1;
    clause_lit_small[c] = NULL;
  }
  for (v = 1; v <= num_vars; ++v)
  {
    var_lit_count[v] = 0;
    var_lit_small[v] = NULL;
    var_neighbor[v] = NULL;
  }
  long long *temp_weight = new long long[num_vars + 10];
  int *temp_lit = new int[num_vars + 10]; // modify local
  string symbol;
  long long degree;
  total_soft_weight_small = 0;

  // 处理负系数
  long long negsum = 0;

  c = 0;

  for (int col = 0; col < consmatrix.getNRows(); ++col)
  {
    // If constraint is <= flip_small to >=
    int signBit = 1;
    if (row_flags[col].test(papilo::RowFlag::kLhsInf))
    {
      signBit = -1;
    }

    const papilo::SparseVectorView<double> row =
        consmatrix.getRowCoefficients(col);
    const double *rowVals = row.getValues();
    const int *indices = row.getIndices();
    const auto len = row.getLength();

    for (int j = 0; j < len; ++j)
    {
      temp_weight[clause_lit_count[c]] = (long long)(rowVals[j]) * signBit;
      temp_lit[clause_lit_count[c]] = indices[j] + 1;
      clause_lit_count[c]++;
    }
    temp_weight[clause_lit_count[c]] = 0;
    temp_lit[clause_lit_count[c]] = 0;
    degree = (((long long)lhs[col]) * signBit);
    org_clause_weight_small[c] = top_clause_weight_small; // 也可以统一一起 区分hard和soft
    int c_equal = 0;
    int c_more = c;
    long long sum = 0;
    long long equal_degree = 0;
    long long equal_temp_weight[clause_lit_count[c] + 10] = {0};
    int equal_temp_lit[clause_lit_count[c] + 10] = {0};
    if (!row_flags[col].test(papilo::RowFlag::kRhsInf) &&
        !row_flags[col].test(papilo::RowFlag::kLhsInf))
    {
      c_more = c + 1;
      i = 0;
      sum = 0;

      while (temp_weight[i] != 0)
      {
        equal_temp_weight[i] = temp_weight[i];
        sum += temp_weight[i];
        i++;
      }
      equal_temp_weight[i] = 0;

      i = 0;
      while (temp_lit[i] != 0)
      {
        equal_temp_lit[i] = -temp_lit[i];
        i++;
      }
      equal_temp_lit[i] = 0;

      clause_lit_count[c_more] = clause_lit_count[c];
      equal_degree = sum - degree;
      org_clause_weight_small[c_more] = top_clause_weight_small;
    }
    negsum = 0;
    i = 0;
    while (temp_weight[i] != 0)
    {
      if (temp_weight[i] < 0)
      {
        negsum += -temp_weight[i];
        temp_weight[i] = -temp_weight[i];
        temp_lit[i] = -temp_lit[i];
      }
      i++;
    }
    degree += negsum;
    clause_true_lit_thres_small[c] = degree;
    if (!row_flags[col].test(papilo::RowFlag::kRhsInf) &&
        !row_flags[col].test(papilo::RowFlag::kLhsInf))
    {
      negsum = 0;
      i = 0;
      while (equal_temp_weight[i] != 0)
      {
        if (equal_temp_weight[i] < 0)
        {
          negsum += -equal_temp_weight[i];
          equal_temp_weight[i] = -equal_temp_weight[i];
          equal_temp_lit[i] = -equal_temp_lit[i];
        }
        i++;
      }
      equal_degree += negsum;
      clause_true_lit_thres_small[c_more] = equal_degree;
    }
    long long max_weight = 0; // find max_weight
    clause_lit_small[c] = new lit_small[clause_lit_count[c] + 1];
    for (i = 0; i < clause_lit_count[c]; ++i)
    {
      clause_lit_small[c][i].clause_num = c;
      clause_lit_small[c][i].var_num = abs(temp_lit[i]);
      clause_lit_small[c][i].weight = temp_weight[i];
      if (temp_weight[i] > max_weight)
        max_weight = temp_weight[i]; // max_weight
      avg_clause_coe_small[c] += double(clause_lit_small[c][i].weight);

      if (temp_lit[i] > 0)
        clause_lit_small[c][i].sense = 1;
      else
        clause_lit_small[c][i].sense = 0;

      var_lit_count[clause_lit_small[c][i].var_num]++;
    }
    clause_max_weight_small[c] = max_weight;
    avg_clause_coe_small[c] =
        round(double(avg_clause_coe_small[c] / (double)clause_lit_count[c]));
    if (avg_clause_coe_small[c] < 1)
      avg_clause_coe_small[c] = 1;
    clause_lit_small[c][i].var_num = 0;
    clause_lit_small[c][i].clause_num = -1;
    clause_lit_small[c][i].weight = 0;
    if (!row_flags[col].test(papilo::RowFlag::kRhsInf) &&
        !row_flags[col].test(papilo::RowFlag::kLhsInf))
    {
      max_weight = 0;
      c = c_more;
      clause_lit_small[c] = new lit_small[clause_lit_count[c] + 1];
      for (i = 0; i < clause_lit_count[c]; ++i)
      {
        clause_lit_small[c][i].clause_num = c;
        clause_lit_small[c][i].var_num = abs(equal_temp_lit[i]);
        clause_lit_small[c][i].weight = equal_temp_weight[i];
        if (equal_temp_weight[i] > max_weight)
          max_weight = equal_temp_weight[i]; // max_weight
        avg_clause_coe_small[c] += double(clause_lit_small[c][i].weight);
        if (equal_temp_lit[i] > 0)
          clause_lit_small[c][i].sense = 1;
        else
          clause_lit_small[c][i].sense = 0;

        var_lit_count[clause_lit_small[c][i].var_num]++;
      }
      clause_max_weight_small[c] = max_weight;
      avg_clause_coe_small[c] =
          round(double(avg_clause_coe_small[c] / (double)clause_lit_count[c]));
      if (avg_clause_coe_small[c] < 1)
        avg_clause_coe_small[c] = 1;
      clause_lit_small[c][i].var_num = 0;
      clause_lit_small[c][i].clause_num = -1;
      clause_lit_small[c][i].weight = 0;
    }
    c++;
  }
  for (int i = 0; i < objective.coefficients.size(); ++i)
  {
    if (objective.coefficients[i] == 0)
      continue;
    clause_lit_count[c] = 1;
    clause_lit_small[c] = new lit_small[clause_lit_count[c] + 1];
    if (objective.coefficients[i] < 0)
    {
      clause_lit_small[c][0].var_num = i + 1;
      clause_lit_small[c][0].clause_num = c;
      clause_lit_small[c][0].weight = 1;
      clause_lit_small[c][0].sense = 1;
      org_clause_weight_small[c] = -objective.coefficients[i];
    }
    else
    {
      clause_lit_small[c][0].var_num = i + 1;
      clause_lit_small[c][0].clause_num = c;
      clause_lit_small[c][0].weight = 1;
      clause_lit_small[c][0].sense = 0;
      org_clause_weight_small[c] = objective.coefficients[i];
    }
    clause_max_weight_small[c] = 1;
    var_lit_count[clause_lit_small[c][0].var_num]++;
    clause_true_lit_thres_small[c] = 1;
    clause_lit_small[c][1].var_num = 0;
    clause_lit_small[c][1].clause_num = -1;
    clause_lit_small[c][1].weight = 0;
    c++;
  }
  delete[] temp_weight; // zyj
  delete[] temp_lit;

  // creat var literal arrays
  for (v = 1; v <= num_vars; ++v)
  {
    var_lit_small[v] = new lit_small[var_lit_count[v] + 1];
    var_lit_count[v] = 0; // reset to 0, for build up the array
  }

  // scan all clauses to build up var literal arrays
  num_hclauses = num_sclauses = 0; // modify
  for (c = 0; c < num_clauses; ++c)
  {
    for (i = 0; i < clause_lit_count[c]; ++i)
    {
      v = clause_lit_small[c][i].var_num;
      var_lit_small[v][var_lit_count[v]] = clause_lit_small[c][i];
      ++var_lit_count[v];
    }
    clause_visied_times[c] = 0; // wyy

    if (org_clause_weight_small[c] != top_clause_weight_small)
    {
      total_soft_weight_small += org_clause_weight_small[c];
      // num_sclauses++; //privious-DeepOpt-v1
      soft_clause_num_index[num_sclauses++] = c; // NuPBO
    }
    else
    {
      hard_clause_num_index[num_hclauses++] = c; // NuPBO
    }
  }
  for (v = 1; v <= num_vars; ++v)
    var_lit_small[v][var_lit_count[v]].clause_num = -1;

  build_neighbor_relation_small();

  best_soln_feasible = 0;
  opt_unsat_weight_small = total_soft_weight_small + 1;
  opt_realobj_small = total_soft_weight_small + 1;
}

void Satlike::postsolve_solution(bool flag_value, bool flag_solution)
{
  printf("c Use postsolve\n");
  papilo::Vec<double> vec = {};
  for (int i = 1; i <= prob.getConstraintMatrix().getNCols(); i++)
  {
    // if(i == 8 || i == 10) vec.push_back(1);
    // else vec.push_back(0);
    // printf("%d", best_soln[i]);
    vec.push_back(best_soln[i]);
  }
  // printf("\n");
  papilo::Solution<double> originSol;
  papilo::Solution<double> reducedSol(std::move(vec));
  papilo::Message msg;
  papilo::Num<double> num;
  msg.setVerbosityLevel(papilo::VerbosityLevel::kQuiet);
  papilo::Postsolve<double> postsolver(msg, num);
  auto originalSolution =
      postsolver.undo(reducedSol, originSol, result.postsolve);
  const papilo::Problem<double> &origprob =
      result.postsolve.getOriginalProblem();
  auto varNames = origprob.getVariableNames();
  if (flag_value)
  {
    long long obj = (long long)origprob.computeSolObjective(originSol.primal);
    if (realobj_small < opt_realobj_small)
    {
      opt_realobj_small = realobj_small;
      printf("o %lld\n", obj);
    }
  }
  if (flag_solution)
  {
    /*printf("v ");
    for (int i = 0; i < originSol.primal.size(); i++)
    {
      if (originSol.primal[i] == 0)
        printf("-");
      printf("%s ", varNames[i].c_str());
    }
    printf("\n");*/
    constexpr int BUF_SIZE = 50000;
    static char buf[BUF_SIZE];
    static int lst = 0;
    // buf[0] = '\n';
    // buf[1] = 'v';
    buf[0] = 'v';
    lst += 1;
    for (int i = 0; i < originSol.primal.size(); i++)
    {
      int sz = strlen(varNames[i].c_str());
      if (lst + sz + 2 >= BUF_SIZE)
      {
        buf[lst++] = '\n';
        lst = write(1, buf, lst);
        buf[0] = 'v';
        lst = 1;
      }
      buf[lst++] = ' ';
      if (originSol.primal[i] == 0)
        buf[lst++] = '-';
      strcpy(buf + lst, varNames[i].c_str());
      lst += sz;
    }
    buf[lst++] = '\n';
    lst = write(1, buf, lst);
    lst = 0;
  }
}
#endif

#endif
