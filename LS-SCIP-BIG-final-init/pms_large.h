#ifndef _PMS_L_H_
#define _PMS_L_H_

#include "basis_pms.h"
#include <algorithm>
#include <cmath>
#include <iomanip>
#include <sstream>

Int ToInt(const std::string &str)
{
  Int result = 0;    // 初始结果为0
  Int sign = Int(1); // 符号位，默认为正数
  size_t i = 0;
  while (i < str.length() && isspace(str[i]))
  {
    i++;
  }
  if (i < str.length() && (str[i] == '+' || str[i] == '-'))
  {
    sign = (str[i] == '-') ? Int(-1) : Int(1);
    i++;
  }
  while (i < str.length() && isdigit(str[i]))
  {
    int digit = str[i] - '0';
    result = result * 10 + digit;
    i++;
  }
  return result * sign;
}

void Satlike::settings_large()
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
  max_clause_score_large = 1000;

  if (num_vars > 2000)
  {
    rdprob = 0.01;
    hd_count_threshold = 15; // 50
    rwprob = 0.1;
    // smooth_probability = 0.0000001;
  }
}

void Satlike::allocate_memory_large()
{
  int malloc_var_length = num_vars + 10;
  int malloc_clause_length = num_clauses + 10;

  // unit_clause = new lit_large[malloc_clause_length];

  var_lit_large = new lit_large *[malloc_var_length];
  var_lit_count = new int[malloc_var_length];
  clause_lit_large = new lit_large *[malloc_clause_length];
  clause_lit_count = new int[malloc_clause_length];
  clause_true_lit_thres_large = new Int[malloc_clause_length];
  clause_visied_times = new int[malloc_clause_length]; // wyy

  hhscore_large = new Int[malloc_var_length]; // hhscore_large
  clause_max_weight_large =
      new Int[malloc_clause_length];                      // 每个子句中的最大系数
  clause_total_sum_large = new Int[malloc_clause_length]; // 每个子句系数之和
  gap1_large = new Int[malloc_clause_length];             // gap1_large
  // best_soln_300 = new int[malloc_var_length];
  // best_soln_1800 = new int[malloc_var_length];
  // opb = new Int[malloc_var_length];

  turb_hardunsat_stack = new int[malloc_clause_length]; // turb_large
  var_mark = new int[malloc_var_length];
  is_selected_clauses = new int[malloc_clause_length];
  selected_var = new int[malloc_var_length];
  turb_best_soln = new int[malloc_var_length];

  score_baocun_large = new Int[10]; // fps
  sscore_baocun_large = new Int[10];
  hhscore_baocun_large = new Int[10];
  score2_large = new Int[malloc_var_length];
  sscore2_large = new Int[malloc_var_length];
  hhscore2_large = new Int[malloc_var_length];
  sat_count2_large = new Int[malloc_clause_length];
  goodvar_stack2 = new int[malloc_var_length];

  clause_score_large = new Int[malloc_clause_length]; // MAB-s
  selected_clauses = new int[malloc_clause_length];
  selected_times = new int[malloc_clause_length];
  sampled_clauses = new int[malloc_clause_length];

  selected_clauses_hard = new int[malloc_clause_length]; // MAB-h
  clause_hard_score_large = new Int[malloc_clause_length];
  selected_times_hard = new int[malloc_clause_length];
  sampled_clauses_hard = new int[malloc_clause_length];

  tune_soft_clause_weight_large = new Int[malloc_clause_length]; // NuPBO
  tuned_degree_unit_weight_large = new Int[malloc_clause_length];
  soft_clause_num_index = new int[malloc_clause_length];
  hard_clause_num_index = new int[malloc_clause_length];
  avg_clause_coe_large = new Int[malloc_clause_length]();

  score_large = new Int[malloc_var_length];
  sscore_large = new Int[malloc_var_length];
  // oscore = new Int[malloc_var_length];
  var_neighbor = new int *[malloc_var_length];
  var_neighbor_count = new int[malloc_var_length];
  time_stamp = new long long[malloc_var_length];
  neighbor_flag = new int[malloc_var_length];
  temp_neighbor = new int[malloc_var_length];

  org_clause_weight_large = new Int[malloc_clause_length];
  clause_weight_large = new Int[malloc_clause_length];
  unit_weight_large = new Int[malloc_clause_length];
  org_unit_weight_large = new Int[malloc_clause_length];
  sat_count_large = new Int[malloc_clause_length];
  // sat_var = new int[malloc_clause_length];
  // clause_selected_count = new Int[malloc_clause_length];
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

void Satlike::free_memory_large()
{
  int i;
  for (i = 0; i < num_clauses; i++)
    delete[] clause_lit_large[i];

  for (i = 1; i <= num_vars; ++i)
  {
    delete[] var_lit_large[i];
    delete[] var_neighbor[i];
  }
  /*hhscore_large*/
  delete[] hhscore_large;
  delete[] clause_max_weight_large;
  delete[] clause_total_sum_large;
  delete[] gap1_large;
  // delete[] best_soln_300;
  // delete[] best_soln_1800;
  // delete[] opb;
  //  delete[] same_big_score;
  /*hhscore_large*/

  delete[] turb_hardunsat_stack; // turb_large
  delete[] var_mark;
  delete[] is_selected_clauses;
  delete[] selected_var;
  delete[] turb_best_soln;

  delete[] score_baocun_large; // fps
  delete[] sscore_baocun_large;
  delete[] hhscore_baocun_large;
  delete[] score2_large;
  delete[] sscore2_large;
  delete[] hhscore2_large;
  delete[] sat_count2_large;
  delete[] goodvar_stack2;

  delete[] tune_soft_clause_weight_large; // NuPBO
  delete[] tuned_degree_unit_weight_large;
  delete[] soft_clause_num_index;
  delete[] hard_clause_num_index;
  delete[] avg_clause_coe_large;

  delete[] clause_score_large; // MAB-s
  delete[] selected_clauses;
  delete[] selected_times;
  delete[] sampled_clauses;

  delete[] selected_clauses_hard; // MAB-h
  delete[] clause_hard_score_large;
  delete[] selected_times_hard;
  delete[] sampled_clauses_hard;

  delete[] var_lit_large;
  delete[] var_lit_count;
  delete[] clause_lit_large;
  delete[] clause_lit_count;
  delete[] clause_true_lit_thres_large;
  delete[] clause_visied_times;

  delete[] score_large;
  // delete[] oscore;
  delete[] sscore_large;
  delete[] var_neighbor;
  delete[] var_neighbor_count;
  delete[] time_stamp;
  delete[] neighbor_flag;
  delete[] temp_neighbor;

  delete[] org_clause_weight_large;
  delete[] clause_weight_large;
  delete[] unit_weight_large;
  delete[] org_unit_weight_large;
  delete[] sat_count_large;
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

void Satlike::build_neighbor_relation_large()
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
      c = var_lit_large[v][i].clause_num;
      for (j = 0; j < clause_lit_count[c]; ++j)
      {
        n = clause_lit_large[c][j].var_num;
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

void Satlike::build_instance_large(char *filename)
{
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
  }
  std::string commentLineTemp;
  bool loadingObj = false;
  Int coeff;
  int newcol = 0;
  num_hclauses = num_hc + num_equal;

  num_sclauses = 0; // 软子句数目为0
  sumneg_min_large = 0;
  top_clause_weight_large = 0; // 最高子句权重为0
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
        coeff = ToInt(s);
      else
      {
        if (coeff > 0)
          top_clause_weight_large += coeff; // top_clause_weight_large = 0 + (+1)
        else
        {
          top_clause_weight_large += (-coeff); // top_clause_weight_large = 0 - (-1)
          sumneg_min_large += (-coeff);
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

  top_clause_weight_large = top_clause_weight_large + 1;

  num_clauses = num_hclauses + num_sclauses;

  allocate_memory_large(); // 加入了hhscore hard+soft+equal+10

  for (c = 0; c < num_clauses; c++)
  {
    clause_lit_count[c] = 0;
    clause_true_lit_thres_large[c] = 1;
    clause_lit_large[c] = NULL;
  }

  for (v = 1; v <= num_vars; ++v)
  {
    var_lit_count[v] = 0;
    var_lit_large[v] = NULL;
    var_neighbor[v] = NULL;
  }

  Int *temp_weight = new Int[num_vars + 10];
  int *temp_lit = new int[num_vars + 10]; // modify local
  // T cur_weight;
  string symbol;
  Int degree;
  total_soft_weight_large = 0;

  // 处理负系数
  Int negsum = 0;

  c = 0;

  while (file >> s)
  {
    // Handle coefficient case
    if (s[0] == '+' || s[0] == '-' || isdigit(s[0]))
      coeff = ToInt(s);
    // Handle bound
    else if (s == ">=" || s == "=")
    {
      symbol = s;
      file >> s;
      temp_weight[clause_lit_count[c]] = 0;
      temp_lit[clause_lit_count[c]] = 0;
      degree = ToInt(s);
      org_clause_weight_large[c] = top_clause_weight_large;
      int c_equal = 0;
      int c_more = c;
      Int sum = 0;
      Int equal_degree = 0;

      Int equal_temp_weight[clause_lit_count[c] + 10] = {0}; // modify
      int equal_temp_lit[clause_lit_count[c] + 10] = {0};

      if (symbol == "=")
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
        org_clause_weight_large[c_more] = top_clause_weight_large;
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
      clause_true_lit_thres_large[c] = degree;
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
        clause_true_lit_thres_large[c_more] = equal_degree;
      }

      Int max_weight = 0; // find max_weight
      clause_lit_large[c] = new lit_large[clause_lit_count[c] + 1];

      for (i = 0; i < clause_lit_count[c]; ++i)
      {
        clause_lit_large[c][i].clause_num = c;
        clause_lit_large[c][i].var_num = abs(temp_lit[i]);
        clause_lit_large[c][i].weight = temp_weight[i];
        if (temp_weight[i] > max_weight)
          max_weight = temp_weight[i]; // max_weight
        avg_clause_coe_large[c] += double(clause_lit_large[c][i].weight);

        if (temp_lit[i] > 0)
          clause_lit_large[c][i].sense = 1;
        else
          clause_lit_large[c][i].sense = 0;

        var_lit_count[clause_lit_large[c][i].var_num]++;
      }

      clause_max_weight_large[c] = max_weight;

      avg_clause_coe_large[c] =
          round(double(avg_clause_coe_large[c] / (double)clause_lit_count[c]));
      if (avg_clause_coe_large[c] < 1)
        avg_clause_coe_large[c] = 1;

      clause_lit_large[c][i].var_num = 0;
      clause_lit_large[c][i].clause_num = -1;
      clause_lit_large[c][i].weight = 0;

      if (symbol == "=")
      {
        max_weight = 0; // find max_weight
        c = c_more;
        clause_lit_large[c] = new lit_large[clause_lit_count[c] + 1];

        for (i = 0; i < clause_lit_count[c]; ++i)
        {
          clause_lit_large[c][i].clause_num = c;
          clause_lit_large[c][i].var_num = abs(equal_temp_lit[i]);
          clause_lit_large[c][i].weight = equal_temp_weight[i];
          if (equal_temp_weight[i] > max_weight)
            max_weight = equal_temp_weight[i]; // max_weight
          avg_clause_coe_large[c] += double(clause_lit_large[c][i].weight);

          if (equal_temp_lit[i] > 0)
            clause_lit_large[c][i].sense = 1;
          else
            clause_lit_large[c][i].sense = 0;

          var_lit_count[clause_lit_large[c][i].var_num]++;
        }

        clause_max_weight_large[c] = max_weight;
        avg_clause_coe_large[c] =
            round(double(avg_clause_coe_large[c] / (double)clause_lit_count[c]));
        if (avg_clause_coe_large[c] < 1)
          avg_clause_coe_large[c] = 1;

        clause_lit_large[c][i].var_num = 0;
        clause_lit_large[c][i].clause_num = -1;
        clause_lit_large[c][i].weight = 0;
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
        coeff = ToInt(s);
      else
      {
        clause_lit_count[c] = 1;
        clause_lit_large[c] = new lit_large[clause_lit_count[c] + 1];
        if (coeff < 0)
        {
          clause_lit_large[c][0].var_num = std::stoi(s.substr(1));
          clause_lit_large[c][0].clause_num = c;
          clause_lit_large[c][0].weight = 1;
          clause_lit_large[c][0].sense = 1;
          org_clause_weight_large[c] = -coeff;
        }
        else
        {
          clause_lit_large[c][0].var_num = std::stoi(s.substr(1));
          clause_lit_large[c][0].clause_num = c;
          clause_lit_large[c][0].weight = 1;
          clause_lit_large[c][0].sense = 0;
          org_clause_weight_large[c] = coeff;
        }
        clause_max_weight_large[c] = 1;
        var_lit_count[clause_lit_large[c][0].var_num]++;
        clause_true_lit_thres_large[c] = 1;
        clause_lit_large[c][1].var_num = 0;
        clause_lit_large[c][1].clause_num = -1;
        clause_lit_large[c][1].weight = 0;
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
    var_lit_large[v] = new lit_large[var_lit_count[v] + 1];
    var_lit_count[v] = 0; // reset to 0, for build up the array
  }

  // scan all clauses to build up var literal arrays
  num_hclauses = num_sclauses = 0; // modify
  for (c = 0; c < num_clauses; ++c)
  {
    for (i = 0; i < clause_lit_count[c]; ++i)
    {
      v = clause_lit_large[c][i].var_num;
      var_lit_large[v][var_lit_count[v]] = clause_lit_large[c][i];
      ++var_lit_count[v];
    }
    clause_visied_times[c] = 0; // wyy

    if (org_clause_weight_large[c] != top_clause_weight_large)
    {
      total_soft_weight_large += org_clause_weight_large[c];
      // num_sclauses++; //privious-DeepOpt-v1
      soft_clause_num_index[num_sclauses++] = c; // NuPBO
    }
    else
    {
      hard_clause_num_index[num_hclauses++] = c; // NuPBO
    }
  }
  for (v = 1; v <= num_vars; ++v)
    var_lit_large[v][var_lit_count[v]].clause_num = -1;

  build_neighbor_relation_large();

  best_soln_feasible = 0;
  opt_unsat_weight_large = total_soft_weight_large + 1;
}

void Satlike::init_large(vector<int> &init_solution)
{
  int v, c;
  int j;
  float initsoftw = 0;

  local_times = 0; // MAB
  if_exceed = 0;
  if_exceed_hard = 0;
  hard_unsat_weight_large = 0; // zyj

  // local_soln_feasible = 0;
  // local_opt_unsat_weight = top_clause_weight_large + 1;
  //  large_weight_clauses_count = 0;
  //  soft_large_weight_clauses_count = 0;

  ave_soft_weight_large = num_sclauses == 0 ? 0 : total_soft_weight_large / num_sclauses;
  ave_hard_weight_large = 0;
  inc_hard_weight_large = 0;
  // cout << "ave soft weight is " << ave_soft_weight_large << endl;

  double tmp_avg_soft_clause_weight = 0.0; // Nupbo-zyj3.7

  tmp_avg_soft_clause_weight = num_sclauses == 0 ? 0 : round(double(top_clause_weight_large - 1) / num_sclauses);
  if (tmp_avg_soft_clause_weight < 1)
    tmp_avg_soft_clause_weight = 1;

  // Initialize clause information
  for (c = 0; c < num_clauses; c++)
  {
    selected_times[c] = 0;          // MAB-s
    clause_score_large[c] = 1;      // MAB-s
    selected_times_hard[c] = 0;     // MAB-hselectd_times_hard
    clause_hard_score_large[c] = 1; // MAB-h

    clause_visied_times[c] = 0;
    // clause_selected_count[c] = 0;

    if (org_clause_weight_large[c] == top_clause_weight_large)
    {
      // clause_weight_large[c] = clause_true_lit_thres_large[c];
      org_unit_weight_large[c] = 1;
      unit_weight_large[c] = org_unit_weight_large[c];
      tuned_degree_unit_weight_large[c] = unit_weight_large[c] / avg_clause_coe_large[c]; // Nupbo-zyj3.7
      Int total_sum = 0;
      for (int i = 0; i < clause_lit_count[c]; ++i)
      {
        total_sum += clause_lit_large[c][i].weight;
      }
      clause_weight_large[c] = total_sum / clause_lit_count[c];
      ave_hard_weight_large += clause_weight_large[c];
      clause_total_sum_large[c] = total_sum; // 硬子句系数之和
    }
    else
    {
      tune_soft_clause_weight_large[c] = double(
          org_clause_weight_large[c] / tmp_avg_soft_clause_weight); // Nupbo-zyj3.7
      unit_weight_large[c] = initsoftw;                             // Nupbo-zyj3.7

      clause_weight_large[c] = org_clause_weight_large[c];
      clause_total_sum_large[c] = org_clause_weight_large[c]; // 软子句系数之和
      org_unit_weight_large[c] =
          ceil((double)clause_weight_large[c] / (double)clause_true_lit_thres_large[c]);
      // unit_weight_large[c] = org_unit_weight_large[c];
    }
    /********min{k + amax, asum}**********/
    if (clause_true_lit_thres_large[c] + clause_max_weight_large[c] <=
        clause_total_sum_large[c])
    {
      gap1_large[c] = clause_true_lit_thres_large[c] + clause_max_weight_large[c];
    }
    else
      gap1_large[c] = clause_total_sum_large[c];
    // gap1_large[c] = min((int)(clause_true_lit_thres_large[c] + clause_max_weight_large[c]),
    // (int)clause_total_sum_large[c]);//gap1_large 一样
    /********min{k + amax, asum}**********/
  }
  inc_hard_weight_large = ave_hard_weight_large % num_hclauses;
  ave_hard_weight_large /= num_hclauses;
  inc_hard_weight_large += ave_soft_weight_large;
  // cout<<"gap1_large"<<gap1_large[3];
  // cout << "inc hard weight is " << inc_hard_weight_large << endl;
  // cout << "ave hard weight is " << ave_hard_weight_large << endl;
  //  for(int i = 0;i < num_clauses;i++)
  //     {
  //    	cout<<"gap1_large "<<i<<" = "<<gap1_large[i]<<endl;
  //     	//cout<<"c_sum "<<i<<"="<<clause_total_sum_large[i]<<endl;
  //     }

  // init_large solution
  //  if (init_solution.size() == 0)
  //  {
  //  if(tries == 1)
  //  {
  //  	for (v = 1; v <= num_vars; v++)
  //  	{
  //  		cur_soln[v] = 0;
  //  		time_stamp[v] = 0;
  //  		unsat_app_count[v] = 0;
  //  	}
  //  }
  //  else if(tries > 1)
  //  {
  //  	for (v = 1; v <= num_vars; v++)
  //  	{
  //  		//cur_soln[v] = init_solution[v];
  //  		// if (cur_soln[v] == 2)
  //  		// 	cur_soln[v] = rand() % 2;
  //  		time_stamp[v] = 0;
  //  		unsat_app_count[v] = 0;
  //  	}
  //  }

  if (init_solution.size() == 0)
  {
    if (best_soln_feasible == 1)
    {
      for (v = 1; v <= num_vars; v++)
      {
        cur_soln[v] = best_soln[v];
        time_stamp[v] = 0;
        // unsat_app_count[v] = 0;
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

  // init_large stacks
  hard_unsat_nb = 0;
  hardunsat_stack_fill_pointer = 0;
  softunsat_stack_fill_pointer = 0;
  unsatvar_stack_fill_pointer = 0;
  /* figure out sat_count_large, sat_var, soft_unsat_weight_large and init_large unsat_stack */
  soft_unsat_weight_large = 0;

  for (c = 0; c < num_clauses; ++c)
  {
    sat_count_large[c] = 0;
    for (j = 0; j < clause_lit_count[c]; ++j)
    {
      if (cur_soln[clause_lit_large[c][j].var_num] == clause_lit_large[c][j].sense)
      {
        sat_count_large[c] += clause_lit_large[c][j].weight;
        // sat_var[c] = clause_lit_large[c][j].var_num;
      }
    }
    if (sat_count_large[c] < clause_true_lit_thres_large[c])
    {
      if (org_clause_weight_large[c] != top_clause_weight_large)
        soft_unsat_weight_large +=
            (clause_true_lit_thres_large[c] - sat_count_large[c]) * org_unit_weight_large[c];
      else
        hard_unsat_weight_large += clause_true_lit_thres_large[c] - sat_count_large[c]; // zyj
      unsat_large(c);
    }
    // cout<<"soft_unsat_weight_large "<<soft_unsat_weight_large<<endl;
  }

  /*figure out score_large*/
  int sense;
  Int weight;

  for (v = 1; v <= num_vars; v++)
  {
    score_large[v] = 0;
    sscore_large[v] = 0;
    hhscore_large[v] = 0; // 初始化hhscore
    for (int i = 0; i < var_lit_count[v]; ++i)
    {
      c = var_lit_large[v][i].clause_num;
      sense = var_lit_large[v][i].sense;
      weight = var_lit_large[v][i].weight;
      if (org_clause_weight_large[c] == top_clause_weight_large) // 加入了hhscore
      {
        if (sat_count_large[c] < clause_true_lit_thres_large[c])
        {
          if (sense != cur_soln[v]) // 当约束不满足时，可以直接加入hhscore
          {
            score_large[v] +=
                double(tuned_degree_unit_weight_large[c] *
                       min(clause_true_lit_thres_large[c] - sat_count_large[c], weight));
            // hhscore_large[v] += unit_weight_large[c] * max(weight -
            // (clause_true_lit_thres_large[c] - sat_count_large[c]), 0);
            hhscore_large[v] += max(weight - (clause_true_lit_thres_large[c] - sat_count_large[c]), Int(0));
          }
          else
          {
            score_large[v] -= double(tuned_degree_unit_weight_large[c] * weight);
            hhscore_large[v] += 0;
          }
        }
        else if (sat_count_large[c] >= clause_true_lit_thres_large[c])
        {
          if (sat_count_large[c] <= gap1_large[c])
          {
            if (sense == cur_soln[v])
            {
              score_large[v] -= double(
                  tuned_degree_unit_weight_large[c] *
                  max(Int(0), clause_true_lit_thres_large[c] - sat_count_large[c] + weight));
              // hhscore_large[v] -= unit_weight_large[c] * min(weight, sat_count_large[c] -
              // clause_true_lit_thres_large[c]);
              hhscore_large[v] -= min(weight, sat_count_large[c] - clause_true_lit_thres_large[c]);
            }
            else
            {
              // hhscore_large[v] += unit_weight_large[c] * min(weight, gap1_large[c] -
              // sat_count_large[c]);
              hhscore_large[v] += min(weight, gap1_large[c] - sat_count_large[c]);
            }
          }
          else if (sat_count_large[c] > gap1_large[c])
          {
            if (sense == cur_soln[v])
            {
              score_large[v] -= tuned_degree_unit_weight_large[c] *
                                max(Int(0), clause_true_lit_thres_large[c] - sat_count_large[c] + weight);
              // hhscore_large[v] -= unit_weight_large[c] * max(weight - (sat_count_large[c] -
              // gap1_large[c]), 0);
              hhscore_large[v] -= max(weight - (sat_count_large[c] - gap1_large[c]), Int(0));
            }
          }
        }
      }
      else
      {
        if (sat_count_large[c] < clause_true_lit_thres_large[c])
        {
          if (sense != cur_soln[v])
          {
            sscore_large[v] += unit_weight_large[c] * tune_soft_clause_weight_large[c];
          }
          else
            sscore_large[v] -= unit_weight_large[c] * tune_soft_clause_weight_large[c];
        }
        else if (sat_count_large[c] >= clause_true_lit_thres_large[c])
        {
          if (sense == cur_soln[v])
          {
            sscore_large[v] -= unit_weight_large[c] * tune_soft_clause_weight_large[c];
          }
        }
      }
    }
  }

  // init_large goodvars stack
  goodvar_stack_fill_pointer = 0;

  for (v = 1; v <= num_vars; v++)
  {
    // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v] > 0)//加入hhscore
    if (score_large[v] + sscore_large[v] > 0)
    {
      already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
      mypush(v, goodvar_stack);
    }
    else
      already_in_goodvar_stack[v] = -1;
  }
}

int Satlike::pick_softc_large()
{
  int sel_c;

  sampled_clauses[0] = softunsat_stack[rand() % softunsat_stack_fill_pointer];
  Int min = clause_score_large[sampled_clauses[0]],
      max = clause_score_large[sampled_clauses[0]];

  for (int i = 1; i < ArmNum; i++) // 20sample min max ???
  {
    sampled_clauses[i] = softunsat_stack[rand() % softunsat_stack_fill_pointer];

    if (clause_score_large[sampled_clauses[i]] < min)
      min = clause_score_large[sampled_clauses[i]];
    if (clause_score_large[sampled_clauses[i]] > max)
      max = clause_score_large[sampled_clauses[i]];
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
        if (clause_weight_large[sampled_clauses[i]] > clause_weight_large[sel_c])
          sel_c = sampled_clauses[i];
      }
    }
  }
  else
  {
    Int max_value =
        clause_score_large[sampled_clauses[0]] +
        lambda * sqrt((log(local_times + 1)) /
                      ((double)(selected_times[sampled_clauses[0]] + 1)));
    sel_c = sampled_clauses[0];
    for (int i = 1; i < ArmNum; i++) // 20个最大的lambda
    {
      Int dtemp =
          clause_score_large[sampled_clauses[i]] +
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
    Int s = pre_unsat_weight_large - soft_unsat_weight_large;
    update_clause_scores_large(s);
  }
  pre_unsat_weight_large = soft_unsat_weight_large;
  local_times++;

  return sel_c;
}

void Satlike::update_clause_scores_large(Int s)
{
  int i, j;
  Int stemp;

  Int opt = opt_unsat_weight_large;
  if (soft_unsat_weight_large < opt)
    opt = soft_unsat_weight_large;

  stemp = s / (pre_unsat_weight_large - opt + 1); // reward

  double discount;
  if (local_times < backward_step)
  {
    for (i = 0; i < local_times; i++)
    {
      discount = pow(gamma, local_times - 1 - i);
      clause_score_large[selected_clauses[i]] += (discount * ((double)stemp));
      if (absInt(clause_score_large[selected_clauses[i]]) > max_clause_score_large)
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
      clause_score_large[selected_clauses[i]] += (discount * ((double)stemp));
      if (absInt(clause_score_large[selected_clauses[i]]) > max_clause_score_large)
        if_exceed = 1;
    }
  }
  if (if_exceed)
  {
    for (i = 0; i < num_clauses; i++)
      clause_score_large[i] = clause_score_large[i] / 2.0;
    if_exceed = 0;
  }
}

int Satlike::pick_hardc_large()
{
  int sel_c;

  sampled_clauses_hard[0] =
      hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
  Int min = clause_hard_score_large[sampled_clauses_hard[0]],
      max = clause_hard_score_large[sampled_clauses_hard[0]];

  for (int i = 1; i < ArmNum; i++) // 20sample min max ???
  {
    sampled_clauses_hard[i] =
        hardunsat_stack[rand() % hardunsat_stack_fill_pointer];

    if (clause_hard_score_large[sampled_clauses_hard[i]] < min)
      min = clause_hard_score_large[sampled_clauses_hard[i]];
    if (clause_hard_score_large[sampled_clauses_hard[i]] > max)
      max = clause_hard_score_large[sampled_clauses_hard[i]];
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
        // if (clause_weight_large[sampled_clauses[i]] > clause_weight_large[sel_c])
        if (rand() % 100 < 50)
          sel_c = sampled_clauses_hard[i];
      }
    }
  }
  else
  {
    Int max_value = clause_hard_score_large[sampled_clauses_hard[0]] +
                    Int(int(lambda * 1000)) * Int(int(sqrt((log(local_times_hard + 1)) / ((double)(selected_times_hard[sampled_clauses_hard[0]] + 1)))) * 1000) / Int(1000) / Int(1000);
    sel_c = sampled_clauses_hard[0];
    for (int i = 1; i < ArmNum; i++) // 20个最大的lambda
    {
      Int dtemp =
          clause_hard_score_large[sampled_clauses_hard[i]] +
          Int(int(lambda * 1000)) *
              Int(int(sqrt((log(local_times_hard + 1)) /
                           ((double)(selected_times_hard[sampled_clauses_hard[i]] +
                                     1)))) *
                  1000) /
              Int(1000) / Int(1000);
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
    // Int s = pre_unsat_weight_large - soft_unsat_weight_large;
    // Int s = pre_unsat_hard_nb - hard_unsat_nb;
    Int s = pre_hard_unsat_weight_large - hard_unsat_weight_large; // zyj
    update_clause_scores_hard_large(s);
  }
  // pre_unsat_weight_large = soft_unsat_weight_large;
  // pre_unsat_hard_nb = hard_unsat_nb;
  pre_hard_unsat_weight_large = hard_unsat_weight_large; // zyj
  local_times_hard++;

  return sel_c;
}

void Satlike::update_clause_scores_hard_large(Int s)
{
  int i, j;
  Int stemp;

  // stemp = ((double)s) / (pre_unsat_hard_nb + 1); // reward
  stemp = s / (pre_hard_unsat_weight_large + 1); // zyj

  double discount;
  if (local_times_hard < backward_step)
  {
    for (i = 0; i < local_times_hard; i++)
    {
      discount = pow(gamma, local_times_hard - 1 - i);
      clause_hard_score_large[selected_clauses_hard[i]] +=
          (Int(int(discount * 1000)) * ((double)stemp) / Int(1000));
      if (absInt(clause_hard_score_large[selected_clauses_hard[i]]) > 1000)
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
      clause_hard_score_large[selected_clauses_hard[i]] +=
          (discount * ((double)stemp));
      if (absInt(clause_hard_score_large[selected_clauses_hard[i]]) > 1000)
        if_exceed_hard = 1;
    }
  }
  if (if_exceed_hard)
  {
    for (i = 0; i < num_clauses; i++)
      clause_hard_score_large[i] = clause_hard_score_large[i] / 2.0;
    if_exceed_hard = 0;
  }
}

void Satlike::pick_vars_large() // new adds
{
  int i, v, j;
  int best_var;
  int rand_select; // 使用hhscore，随机选择
  int mark_v1 = 0;
  int mark_v2 = 0;
  // int better_var1;

  update_clause_weights_large();
  int sel_c;
  int sel_c_set[100];
  lit_large *p;
  int mark_which = 0;
  if (hardunsat_stack_fill_pointer > 0)
  {
    // if (step < 10000 || best_soln_feasible > 0) // MAB-h
    // if (best_soln_feasible > 0) // MAB-h
    // {
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
    // }
    // else
    // {
    //   // 一定概率扰动
    //   if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
    //   {
    //     sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
    //   }
    //   else
    //     sel_c = pick_hardc_large(); // zyj-MABh
    //   mark_which = 1;
    //   // cout << "MAB-h" << sel_c;
    // }
  }
  else
  {
    // sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
    sel_c = pick_softc_large();
    mark_which = 3;
  }

  if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
  {
    best_var = clause_lit_large[sel_c][rand() % clause_lit_count[sel_c]].var_num;
    flip_large(best_var);
    return;
  }
  // return clause_lit_large[sel_c][rand() % clause_lit_count[sel_c]].var_num;

  if (clause_lit_count[sel_c] == 1)
  {
    best_var = clause_lit_large[sel_c][0].var_num;
    flip_large(best_var);
    return;
  }
  else if (clause_lit_count[sel_c] == 2)
  {
    int v1 = clause_lit_large[sel_c][0].var_num;
    int v2 = clause_lit_large[sel_c][1].var_num;
    if (rand() % 100 < 0)
    {
      if (rand() % 100 < 50)
        best_var = v1;
      else
        best_var = v2;
    }
    else
    {
      score_baocun_large[0] = score_large[v1]; // baocun score_large
      sscore_baocun_large[0] = sscore_large[v1];
      hhscore_baocun_large[0] = hhscore_large[v1];
      score_baocun_large[1] = score_large[v2];
      sscore_baocun_large[1] = sscore_large[v2];
      hhscore_baocun_large[1] = hhscore_large[v2];
      for (i = 0; i < num_vars; i++)
      {
        goodvar_stack2[i] = 0;
      }

      int best_v1_neighbor;
      int best_v2_neighbor;
      flip_fps_large(v1);
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
            if (score2_large[v] + sscore2_large[v] >
                score2_large[best_v1_neighbor] +
                    sscore2_large[best_v1_neighbor]) /*New Added*/
              best_v1_neighbor = v;
            else if (score2_large[v] + sscore2_large[v] ==
                     score2_large[best_v1_neighbor] +
                         sscore2_large[best_v1_neighbor]) /*New Added*/
            {
              // if (time_stamp[v] < time_stamp[vars2[i]])//hhscore_large
              // best_v1_neighbor = v;
              if (hhscore2_large[v] > hhscore2_large[best_v1_neighbor])
              {
                best_v1_neighbor = v;
              }
              else if (hhscore2_large[v] == hhscore2_large[best_v1_neighbor])
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
            if (score2_large[v] + sscore2_large[v] >
                score2_large[best_v1_neighbor] +
                    sscore2_large[best_v1_neighbor]) /*New Added*/
              best_v1_neighbor = v;
            else if (score2_large[v] + sscore2_large[v] ==
                     score2_large[best_v1_neighbor] +
                         sscore2_large[best_v1_neighbor]) /*New Added*/
            {
              if (hhscore2_large[v] > hhscore2_large[best_v1_neighbor])
              {
                best_v1_neighbor = v;
              }
              else if (hhscore2_large[v] == hhscore2_large[best_v1_neighbor])
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
        score_baocun_large[0] += score2_large[best_v1_neighbor];
        sscore_baocun_large[0] += sscore2_large[best_v1_neighbor]; /*New Added*/
        hhscore_baocun_large[0] += hhscore2_large[best_v1_neighbor];
      }
      else
      {
        mark_v1 = 0;
      }

      for (i = 0; i < num_vars; i++)
      {
        goodvar_stack2[i] = 0;
      }

      flip_fps_large(v2);
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
            if (score2_large[v] + sscore2_large[v] >
                score2_large[best_v2_neighbor] +
                    sscore2_large[best_v2_neighbor]) /*New Added*/
              best_v2_neighbor = v;
            else if (score2_large[v] + sscore2_large[v] ==
                     score2_large[best_v2_neighbor] +
                         sscore2_large[best_v2_neighbor]) /*New Added*/
            {
              if (hhscore2_large[v] > hhscore2_large[best_v2_neighbor])
              {
                best_v2_neighbor = v;
              }
              else if (hhscore2_large[v] == hhscore2_large[best_v2_neighbor])
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
            if (score2_large[v] + sscore2_large[v] >
                score2_large[best_v2_neighbor] +
                    sscore2_large[best_v2_neighbor]) /*New Added*/
              best_v2_neighbor = v;
            else if (score2_large[v] + sscore2_large[v] ==
                     score2_large[best_v2_neighbor] +
                         sscore2_large[best_v2_neighbor]) /*New Added*/
            {
              if (hhscore2_large[v] > hhscore2_large[best_v2_neighbor])
              {
                best_v2_neighbor = v;
              }
              else if (hhscore2_large[v] == hhscore2_large[best_v2_neighbor])
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
        score_baocun_large[1] += score2_large[best_v2_neighbor];
        sscore_baocun_large[1] += sscore2_large[best_v2_neighbor]; /*New Added*/
        hhscore_baocun_large[1] += hhscore2_large[best_v2_neighbor];
      }
      else
      {
        mark_v2 = 0;
      }
      // int best_flip_neighbor;
      // int best_flip;
      if (mark_v1 == 1 && mark_v2 == 1)
      {
        if (score_baocun_large[0] + sscore_baocun_large[0] > 0 &&
            score_baocun_large[1] + sscore_baocun_large[1] > 0)
        {
          if (score_baocun_large[0] + sscore_baocun_large[0] >
              score_baocun_large[1] + sscore_baocun_large[1])
          {
            best_flip_neighbor = best_v1_neighbor;
            best_var = v1;
          }
          else if (score_baocun_large[0] + sscore_baocun_large[0] <
                   score_baocun_large[1] + sscore_baocun_large[1])
          {
            best_flip_neighbor = best_v2_neighbor;
            best_var = v2;
          }
          else
          {
            if (hhscore_baocun_large[0] > hhscore_baocun_large[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
            }
            else if (hhscore_baocun_large[0] < hhscore_baocun_large[1])
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
          flip_large(best_var);
          flip_large(best_flip_neighbor);
          return;
        }
        else if (score_baocun_large[0] + sscore_baocun_large[0] > 0 &&
                 score_baocun_large[1] + sscore_baocun_large[1] < 0)
        {
          best_flip_neighbor = best_v1_neighbor;
          best_var = v1;
          flip_large(best_var);
          flip_large(best_flip_neighbor);
          return;
        }
        else if (score_baocun_large[0] + sscore_baocun_large[0] < 0 &&
                 score_baocun_large[1] + sscore_baocun_large[1] > 0)
        {
          best_flip_neighbor = best_v2_neighbor;
          best_var = v2;
          flip_large(best_var);
          flip_large(best_flip_neighbor);
          return;
        }
        else // new addflip
        {
          if (score_large[v1] + sscore_large[v1] < score_baocun_large[0] + sscore_baocun_large[0] &&
              score_large[v2] + sscore_large[v2] < score_baocun_large[1] + sscore_baocun_large[1])
          {
            if (score_baocun_large[0] + sscore_baocun_large[0] >
                score_baocun_large[1] + sscore_baocun_large[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
            else if (score_baocun_large[0] + sscore_baocun_large[0] <
                     score_baocun_large[1] + sscore_baocun_large[1])
            {
              best_flip_neighbor = best_v2_neighbor;
              best_var = v2;
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
            else // 可以用hhscore or rand or teacher
            {
              if (hhscore_baocun_large[0] > hhscore_baocun_large[1])
              {
                best_flip_neighbor = best_v1_neighbor;
                best_var = v1;
              }
              else if (hhscore_baocun_large[0] < hhscore_baocun_large[1])
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
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
          }
          else
          {
            if (score_large[v1] + sscore_large[v1] > score_large[v2] + sscore_large[v2])
            {
              best_var = v1;
            }
            else if (score_large[v1] + sscore_large[v1] < score_large[v2] + sscore_large[v2])
            {
              best_var = v2;
            }
            else
            {
              if (hhscore_large[v1] > hhscore_large[v2])
              {
                best_var = v1;
              }
              else if (hhscore_large[v1] < hhscore_large[v2])
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
            flip_large(best_var);
            return;
          }
          // if(score_large[v1] + sscore_large[v1] > score_large[v2] + sscore_large[v2])
          // {
          // 	best_var = v1;
          // }
          // else if(score_large[v1] + sscore_large[v1] < score_large[v2] + sscore_large[v2])
          // {
          // 	best_var = v2;
          // }
          // else
          // {
          // 	if(hhscore_large[v1] > hhscore_large[v2])
          // 	{
          // 		best_var = v1;
          // 	}
          // 	else if(hhscore_large[v1] < hhscore_large[v2])
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
          // flip_large(best_var);
          // return;
        }

        //  if (scores[i] + sscores[i] > 0)
        //  {    /*New Added*/
        //  	flip_large(best_vars[i]);
        //  	flip_large(vars2[i]);
        //  	time_stamp[best_vars[i]] = step;
        //  	time_stamp[vars2[i]] = step;
        //  	return;
      }
      else if (mark_v1 == 1 && mark_v2 == 0)
      {
        if (score_baocun_large[0] + sscore_baocun_large[0] > 0)
        {
          best_var = v1;
          best_flip_neighbor = best_v1_neighbor;
          flip_large(best_var);
          flip_large(best_flip_neighbor);
          return;
        }
        else // new addflip
        {
          if (score_large[v1] + sscore_large[v1] < score_baocun_large[0] + sscore_baocun_large[0] &&
              score_large[v2] + sscore_large[v2] < score_baocun_large[1] + sscore_baocun_large[1])
          {
            if (score_baocun_large[0] + sscore_baocun_large[0] >
                score_baocun_large[1] + sscore_baocun_large[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
            else if (score_baocun_large[0] + sscore_baocun_large[0] <
                     score_baocun_large[1] + sscore_baocun_large[1])
            {
              best_flip_neighbor = best_v2_neighbor;
              best_var = v2;
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
            else
            {
              if (hhscore_baocun_large[0] > hhscore_baocun_large[1])
              {
                best_flip_neighbor = best_v1_neighbor;
                best_var = v1;
              }
              else if (hhscore_baocun_large[0] < hhscore_baocun_large[1])
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
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
          }
          else
          {
            if (score_large[v1] + sscore_large[v1] > score_large[v2] + sscore_large[v2])
            {
              best_var = v1;
            }
            else if (score_large[v1] + sscore_large[v1] < score_large[v2] + sscore_large[v2])
            {
              best_var = v2;
            }
            else
            {
              if (hhscore_large[v1] > hhscore_large[v2])
              {
                best_var = v1;
              }
              else if (hhscore_large[v1] < hhscore_large[v2])
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
            flip_large(best_var);
            return;
          }
          // if(score_large[v1] + sscore_large[v1] > score_large[v2] + sscore_large[v2])
          // {
          // 	best_var = v1;
          // }
          // else if(score_large[v1] + sscore_large[v1] < score_large[v2] + sscore_large[v2])
          // {
          // 	best_var = v2;
          // }
          // else
          // {
          // 	if(hhscore_large[v1] > hhscore_large[v2])
          // 	{
          // 		best_var = v1;
          // 	}
          // 	else if(hhscore_large[v1] < hhscore_large[v2])
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
          // flip_large(best_var);
          // return;
        }
      }
      else if (mark_v1 == 0 && mark_v2 == 1)
      {
        if (score_baocun_large[1] + sscore_baocun_large[1] > 0)
        {
          best_var = v2;
          best_flip_neighbor = best_v2_neighbor;
          flip_large(best_var);
          flip_large(best_flip_neighbor);
          return;
        }
        else // new addflip
        {
          if (score_large[v1] + sscore_large[v1] < score_baocun_large[0] + sscore_baocun_large[0] &&
              score_large[v2] + sscore_large[v2] < score_baocun_large[1] + sscore_baocun_large[1])
          {
            if (score_baocun_large[0] + sscore_baocun_large[0] >
                score_baocun_large[1] + sscore_baocun_large[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
            else if (score_baocun_large[0] + sscore_baocun_large[0] <
                     score_baocun_large[1] + sscore_baocun_large[1])
            {
              best_flip_neighbor = best_v2_neighbor;
              best_var = v2;
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
            else
            {
              if (hhscore_baocun_large[0] > hhscore_baocun_large[1])
              {
                best_flip_neighbor = best_v1_neighbor;
                best_var = v1;
              }
              else if (hhscore_baocun_large[0] < hhscore_baocun_large[1])
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
              flip_large(best_var);
              flip_large(best_flip_neighbor);
              return;
            }
          }
          else
          {
            if (score_large[v1] + sscore_large[v1] > score_large[v2] + sscore_large[v2])
            {
              best_var = v1;
            }
            else if (score_large[v1] + sscore_large[v1] < score_large[v2] + sscore_large[v2])
            {
              best_var = v2;
            }
            else
            {
              if (hhscore_large[v1] > hhscore_large[v2])
              {
                best_var = v1;
              }
              else if (hhscore_large[v1] < hhscore_large[v2])
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
            flip_large(best_var);
            return;
          }
          // if(score_large[v1] + sscore_large[v1] > score_large[v2] + sscore_large[v2])
          // {
          // 	best_var = v1;
          // }
          // else if(score_large[v1] + sscore_large[v1] < score_large[v2] + sscore_large[v2])
          // {
          // 	best_var = v2;
          // }
          // else
          // {
          // 	if(hhscore_large[v1] > hhscore_large[v2])
          // 	{
          // 		best_var = v1;
          // 	}
          // 	else if(hhscore_large[v1] < hhscore_large[v2])
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
          // flip_large(best_var);
          // return;
        }
      }
      else // new added
      {
        if (score_large[v1] + sscore_large[v1] < score_baocun_large[0] + sscore_baocun_large[0] &&
            score_large[v2] + sscore_large[v2] < score_baocun_large[1] + sscore_baocun_large[1])
        {
          if (score_baocun_large[0] + sscore_baocun_large[0] >
              score_baocun_large[1] + sscore_baocun_large[1])
          {
            best_flip_neighbor = best_v1_neighbor;
            best_var = v1;
            flip_large(best_var);
            flip_large(best_flip_neighbor);
            return;
          }
          else if (score_baocun_large[0] + sscore_baocun_large[0] <
                   score_baocun_large[1] + sscore_baocun_large[1])
          {
            best_flip_neighbor = best_v2_neighbor;
            best_var = v2;
            flip_large(best_var);
            flip_large(best_flip_neighbor);
            return;
          }
          else
          {
            if (hhscore_baocun_large[0] > hhscore_baocun_large[1])
            {
              best_flip_neighbor = best_v1_neighbor;
              best_var = v1;
            }
            else if (hhscore_baocun_large[0] < hhscore_baocun_large[1])
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
            flip_large(best_var);
            flip_large(best_flip_neighbor);
            return;
          }
        }
        else
        {
          if (score_large[v1] + sscore_large[v1] > score_large[v2] + sscore_large[v2])
          {
            best_var = v1;
          }
          else if (score_large[v1] + sscore_large[v1] < score_large[v2] + sscore_large[v2])
          {
            best_var = v2;
          }
          else
          {
            if (hhscore_large[v1] > hhscore_large[v2])
            {
              best_var = v1;
            }
            else if (hhscore_large[v1] < hhscore_large[v2])
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
          flip_large(best_var);
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

      best_var = clause_lit_large[sel_c][rand() % clause_lit_count[sel_c]].var_num;
      for (i = 1; i < bms; i++)
      {
        v = clause_lit_large[sel_c][rand() % clause_lit_count[sel_c]].var_num;
        if (score_large[v] + sscore_large[v] > score_large[best_var] + sscore_large[best_var])
          best_var = v;
        else if (score_large[v] + sscore_large[v] == score_large[best_var] + sscore_large[best_var])
        {
          if (hhscore_large[v] > hhscore_large[best_var])
          {
            best_var = v;
          }
          else if (hhscore_large[v] == hhscore_large[best_var])
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
          clause_lit_large[sel_c_set[0]][rand() % clause_lit_count[sel_c_set[0]]]
              .var_num;
      for (j = 0; j < 100; j++)
      {
        // int bms = (clause_lit_count[sel_c_set[j]] - 1) / 2 + 1;
        // //选择子句的变量个数除2，向上取整 best_var = clause_lit_large[sel_c][rand()
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
          v = clause_lit_large[sel_c_set[j]][rand() % clause_lit_count[sel_c_set[j]]]
                  .var_num;
          if (score_large[v] + sscore_large[v] > score_large[best_var] + sscore_large[best_var])
            best_var = v;
          else if (score_large[v] + sscore_large[v] == score_large[best_var] + sscore_large[best_var])
          {
            if (hhscore_large[v] > hhscore_large[best_var])
            {
              best_var = v;
            }
            else if (hhscore_large[v] == hhscore_large[best_var])
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
    flip_large(best_var);
    return;
  }
  /********BMS********/
  // flip_large(best_var);
  // return;
}

int Satlike::pick_var_large() // new adds
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
        if (score_large[v] + sscore_large[v] > score_large[best_var] + sscore_large[best_var])
          best_var = v;
        else if (score_large[v] + sscore_large[v] == score_large[best_var] + sscore_large[best_var])
        {
          if (hhscore_large[v] > hhscore_large[best_var])
          {
            best_var = v;
          }
          else if (hhscore_large[v] == hhscore_large[best_var])
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
        if (score_large[v] + sscore_large[v] > score_large[best_var] + sscore_large[best_var])
          best_var = v;
        else if (score_large[v] + sscore_large[v] == score_large[best_var] + sscore_large[best_var])
        {
          if (hhscore_large[v] > hhscore_large[best_var])
          {
            best_var = v;
          }
          else if (hhscore_large[v] == hhscore_large[best_var])
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

  update_clause_weights_large();

  int sel_c;
  int sel_c_set[100];
  lit_large *p;
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
    sel_c = pick_softc_large(); // MAB
    mark_which = 3;
  }
  if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
    return clause_lit_large[sel_c][rand() % clause_lit_count[sel_c]].var_num;

  if (clause_lit_count[sel_c] == 1)
  {
    best_var = clause_lit_large[sel_c][0].var_num;
  }
  else if (clause_lit_count[sel_c] == 2)
  {
    int v1 = clause_lit_large[sel_c][0].var_num;
    int v2 = clause_lit_large[sel_c][1].var_num;
    if (rand() % 100 < 0)
    {
      if (rand() % 100 < 50)
        best_var = v1;
      else
        best_var = v2;
    }
    else
    {

      if (score_large[v1] + sscore_large[v1] > score_large[v2] + sscore_large[v2])
      {
        best_var = v1;
      }
      else if (score_large[v1] + sscore_large[v1] < score_large[v2] + sscore_large[v2])
      {
        best_var = v2;
      }
      else
      {
        if (hhscore_large[v1] > hhscore_large[v2])
        {
          best_var = v1;
        }
        else if (hhscore_large[v1] < hhscore_large[v2])
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
                  int v1 = clause_lit_large[sel_c][0].var_num;
                  int v2 = clause_lit_large[sel_c][1].var_num;

                  //if(time_stamp[v1] + 55  > step)
                  //	best_var = v2;
                  //else if(time_stamp[v2] + 5  > step)
                  //	best_var = v1;
                  //else
                  if(score_large[v1] + sscore_large[v1] == score_large[v2] + sscore_large[v2])
                          best_var = clause_lit_large[sel_c][rand() % 2].var_num;
                  else if(score_large[v1] + sscore_large[v1] < 0 && score_large[v2] + sscore_large[v2]
     >= 0) best_var = v2; else if(score_large[v2] + sscore_large[v2] < 0 && score_large[v1] +
     sscore_large[v1] >= 0) best_var = v1; else if(score_large[v1] + sscore_large[v1] < 0 &&
     score_large[v2] + sscore_large[v2] < 0){ int tt = -(score_large[v1] + sscore_large[v1] +
     score_large[v2] + sscore_large[v2]); int rand_num = rand() % tt; if(rand_num < -1 *
     score_large[v1] - sscore_large[v1]) best_var = v2; else best_var = v1;
                  }
                  else{
                          int tt = score_large[v1] + sscore_large[v1] + score_large[v2] +
     sscore_large[v2]; int rand_num = rand() % tt; if(rand_num < score_large[v1] +
     sscore_large[v1]) best_var = v1; else best_var = v2;
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

      best_var = clause_lit_large[sel_c][rand() % clause_lit_count[sel_c]].var_num;
      for (i = 1; i < bms; i++)
      {
        v = clause_lit_large[sel_c][rand() % clause_lit_count[sel_c]].var_num;
        if (score_large[v] + sscore_large[v] > score_large[best_var] + sscore_large[best_var])
          best_var = v;
        else if (score_large[v] + sscore_large[v] == score_large[best_var] + sscore_large[best_var])
        {
          if (hhscore_large[v] > hhscore_large[best_var])
          {
            best_var = v;
          }
          else if (hhscore_large[v] == hhscore_large[best_var])
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
          clause_lit_large[sel_c_set[0]][rand() % clause_lit_count[sel_c_set[0]]]
              .var_num;
      for (j = 0; j < 100; j++)
      {
        // int bms = (clause_lit_count[sel_c_set[j]] - 1) / 2 + 1;
        // //选择子句的变量个数除2，向上取整 best_var = clause_lit_large[sel_c][rand()
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
          v = clause_lit_large[sel_c_set[j]][rand() % clause_lit_count[sel_c_set[j]]]
                  .var_num;
          if (score_large[v] + sscore_large[v] > score_large[best_var] + sscore_large[best_var])
            best_var = v;
          else if (score_large[v] + sscore_large[v] == score_large[best_var] + sscore_large[best_var])
          {
            if (hhscore_large[v] > hhscore_large[best_var])
            {
              best_var = v;
            }
            else if (hhscore_large[v] == hhscore_large[best_var])
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

  /*best_var = clause_lit_large[sel_c][0].var_num;
  p = clause_lit_large[sel_c];
  for (p++; (v = p->var_num) != 0; p++)
  {
          if (score_large[v] + sscore_large[v] > score_large[best_var] + sscore_large[best_var])
                  best_var = v;
          else if (score_large[v] + sscore_large[v] == score_large[best_var] + sscore_large[best_var])
          {
                  if(hhscore_large[v] > hhscore_large[best_var])
                  {
                          best_var = v;
                  }else if(hhscore_large[v] == hhscore_large[best_var])
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

void Satlike::flip_fps_large(
    int flipvar) // /*New Added：根据flip2进行了修改*/ 试探性假翻转！
{
  int i, v, c;
  int index;
  lit_large *clause_c;
  Int weight;
  Int gap;

  Int org_flipvar_score = score_large[flipvar];
  Int org_sscore = sscore_large[flipvar];
  Int org_hhscore = hhscore_large[flipvar];  /*待翻转变量的软子句得分*/
  cur_soln[flipvar] = 1 - cur_soln[flipvar]; // 翻转变量flipvar

  for (i = 0; i < var_neighbor_count[flipvar];
       i++)
  { // score2和sscore2临时记录flipvar的所有邻居得分
    score2_large[var_neighbor[flipvar][i]] = score_large[var_neighbor[flipvar][i]];
    sscore2_large[var_neighbor[flipvar][i]] = sscore_large[var_neighbor[flipvar][i]];
    hhscore2_large[var_neighbor[flipvar][i]] = hhscore_large[var_neighbor[flipvar][i]];
  }

  for (i = 0; i < var_lit_count[flipvar]; i++) /*New Added*/
  {
    c = var_lit_large[flipvar][i].clause_num;
    sat_count2_large[c] = sat_count_large[c];
  }

  for (i = 0; i < var_lit_count[flipvar]; ++i) // 对于flipvar的每一个文字
  {
    c = var_lit_large[flipvar][i].clause_num;
    clause_c = clause_lit_large[c];
    weight = var_lit_large[flipvar][i].weight;

    if (org_clause_weight_large[c] == top_clause_weight_large) // 硬子句c
    {
      if (cur_soln[flipvar] ==
          var_lit_large[flipvar][i]
              .sense) // （翻转完后）当前解中变量flipvar的值，等于变量文字数组中变量flipvar的第i个文字的属性【翻转变量flipvar满足】
      {
        // if (org_clause_weight_large[c] != top_clause_weight_large && sat_count_large[c] <
        // clause_true_lit_thres_large[c]) //？？？冗余，可以删除
        // {
        // 	//soft_unsat_weight是否需要复制？
        // 	soft_unsat_weight_large -= org_unit_weight_large[c] * min(weight,
        // clause_true_lit_thres_large[c] - sat_count_large[c]);
        // }
        // sat_count_large[c] += weight;
        if (sat_count2_large[c] + weight <=
            clause_true_lit_thres_large
                [c]) // 若硬子句c的满足计数+变量flipvar的第i个文字的权重<=硬子句c的度
        {
          gap = clause_true_lit_thres_large[c] -
                sat_count2_large[c]; // gap，置为硬子句c的度-硬子句c的满足计数
          for (
              lit_large *p = clause_c; (v = p->var_num) != 0;
              p++) // 对于硬子句c的每个文字p（对应变量v）（根据翻转flipvar后的结果，更新硬子句c中所有变量的得分）
          {
            if (p->sense !=
                cur_soln
                    [v]) // 若文字p的属性，不等于当前解中变量v的值【变量p不满足】
            {
              score2_large[v] -=
                  double((tuned_degree_unit_weight_large[c] *
                          (min(gap, p->weight) -
                           min(gap - weight, p->weight)))); // 变量v的硬子句得分，累积减去(硬子句c的单元权重*(min(gap,
                                                            // 文字p的权重)-min(gap-文字i的权重,
                                                            // 文字p的权重)))
              hhscore2_large[v] += ((max(p->weight - gap + weight, Int(0)) -
                                     max(p->weight - gap, Int(0))));
            }
          }
        }
        else if (sat_count2_large[c] <=
                 clause_true_lit_thres_large[c]) // sat_count_large[c]+weight >
                                                 // clause_true_lit_thres_large[c]
        {
          gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score2_large[v] -=
                  double((tuned_degree_unit_weight_large[c] * min(gap, p->weight)));
              // hhscore_large[v] += (unit_weight_large[c] * (min(p->weight, gap1_large[c] -
              // sat_count_large[c] - weight) - max(p->weight - gap, 0)));//2 unsat_large
              hhscore2_large[v] +=
                  ((min(p->weight, gap1_large[c] - sat_count2_large[c] - weight) -
                    max(p->weight - gap, Int(0)))); // 2 unsat_large
            }
            else
            {
              score2_large[v] +=
                  double(tuned_degree_unit_weight_large[c] *
                         (p->weight - max(Int(0), gap - weight + p->weight)));
              // hhscore_large[v] -= unit_weight_large[c] * min(p->weight, weight - gap);//2
              // sat_large
              hhscore2_large[v] -= min(p->weight, weight - gap); // 2 sat_large
            }
          }
        }
        else // sat_count_large[c]+weight > clause_true_lit_thres_large[c], sat_count_large[c] >
             // clause_true_lit_thres_large[c]
        {
          /**************hhscore_large****************/
          // ��ǰ��satL>k�Լ�satL+weight>k�����
          if (sat_count2_large[c] <= gap1_large[c]) // ע��Ⱥ� (2)
          {
            // gap = clause_true_lit_thres_large[c] - sat_count_large[c];
            if (sat_count2_large[c] + weight <= gap1_large[c]) // ע��Ⱥ�  ��ǰ�ǣ�2��-��2��
            {
              gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
              for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score2_large[v] += double(tuned_degree_unit_weight_large[c] *
                                            (max(Int(0), gap + p->weight) -
                                             max(Int(0), gap - weight + p->weight)));
                  // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, -gap) -
                  // min(p->weight, weight - gap));//4
                  hhscore2_large[v] += (min(p->weight, -gap) -
                                        min(p->weight, weight - gap)); // 4
                }
                else
                {
                  // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, gap1_large[c] -
                  // sat_count_large[c] - weight) - min(p->weight, gap1_large[c] -
                  // sat_count_large[c]));//3
                  hhscore2_large[v] +=
                      (min(p->weight, gap1_large[c] - sat_count2_large[c] - weight) -
                       min(p->weight, gap1_large[c] - sat_count2_large[c])); // 3
                }
              }
            }
            else if (sat_count2_large[c] + weight > gap1_large[c]) //(2)-(3)
            {
              gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
              for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score2_large[v] += double(tuned_degree_unit_weight_large[c] *
                                            (max(Int(0), gap + p->weight) -
                                             max(Int(0), gap - weight + p->weight)));
                  // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, -gap) -
                  // max(p->weight - weight - sat_count_large[c] + gap , 0));//5
                  hhscore2_large[v] += (min(p->weight, -gap) - max(p->weight - weight - sat_count2_large[c] + gap, Int(0))); // 5
                }
                else
                {
                  // hhscore_large[v] -= unit_weight_large[c] * (min(p->weight, gap1_large[c] -
                  // sat_count_large[c]));//6
                  hhscore2_large[v] -=
                      (min(p->weight, gap1_large[c] - sat_count2_large[c])); // 6
                }
              }
            }
          }
          else if (sat_count2_large[c] > gap1_large[c]) //(3) - (3)
          {
            gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
            for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
            {
              if (p->sense == cur_soln[v])
              {
                score2_large[v] += double(tuned_degree_unit_weight_large[c] *
                                          (max(Int(0), gap + p->weight) -
                                           max(Int(0), gap - weight + p->weight)));
                // hhscore_large[v] += unit_weight_large[c] * (max(p->weight - sat_count_large[c]
                // + gap1_large[c] , 0) - max(p->weight - sat_count_large[c] - weight +
                // gap1_large[c], 0));//7
                hhscore2_large[v] +=
                    (max(p->weight - sat_count2_large[c] + gap1_large[c], Int(0)) -
                     max(p->weight - sat_count2_large[c] - weight + gap1_large[c],
                         Int(0))); // 7
              }
            }
          }
        }
        sat_count2_large[c] += weight;
        /*New Added*/ // 硬子句c的满足计数，累积加上文字i的权重
      }
      else // （翻转后）cur_soln[flipvar] != cur_lit.sense
      {
        //--sat_count_large[c];
        // if (org_clause_weight_large[c] != top_clause_weight_large && sat_count_large[c] -
        // weight < clause_true_lit_thres_large[c]) //？？？
        // {
        // 	//soft_unsat_weight是否需要复制？
        // 	soft_unsat_weight_large += org_unit_weight_large[c] * min(weight,
        // clause_true_lit_thres_large[c] - sat_count_large[c] + weight);
        // }

        if (sat_count2_large[c] - weight >= clause_true_lit_thres_large[c])
        {
          // gap = clause_true_lit_thres_large[c] - sat_count_large[c];
          /***************hhscore_large*************/
          if (sat_count2_large[c] > gap1_large[c]) //(3)
          {
            if (sat_count2_large[c] - weight > gap1_large[c]) //(3) - (3)  ע��Ⱥ�
            {
              gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
              for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score2_large[v] -= double(tuned_degree_unit_weight_large[c] *
                                            (max(Int(0), gap + weight + p->weight) -
                                             max(Int(0), gap + p->weight)));
                  // hhscore_large[v] += unit_weight_large[c] * (max(p->weight -
                  // sat_count_large[c] + gap1_large[c], 0) - max(p->weight - sat_count_large[c] +
                  // weight + gap1_large[c], 0));//8
                  hhscore2_large[v] +=
                      (max(p->weight - sat_count2_large[c] + gap1_large[c], Int(0)) -
                       max(p->weight - sat_count2_large[c] + weight + gap1_large[c],
                           Int(0))); // 8
                }
              }
            }
            else if (sat_count2_large[c] - weight <= gap1_large[c]) //(3) - (2)
            {
              gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
              for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score2_large[v] -= double(tuned_degree_unit_weight_large[c] *
                                            (max(Int(0), gap + weight + p->weight) -
                                             max(Int(0), gap + p->weight)));
                  // hhscore_large[v] += unit_weight_large[c] * (max(p->weight -
                  // sat_count_large[c] + gap1_large[c], 0) - min(p->weight, sat_count_large[c] -
                  // weight - sat_count_large[c]));//9
                  hhscore2_large[v] +=
                      (max(p->weight - sat_count2_large[c] + gap1_large[c], Int(0)) -
                       min(p->weight,
                           sat_count2_large[c] - weight - sat_count2_large[c])); // 9
                }
                else
                {
                  // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, gap1_large[c] -
                  // sat_count_large[c] + weight));//10
                  hhscore2_large[v] += (min(p->weight, gap1_large[c] - sat_count2_large[c] + weight)); // 10
                }
              }
            }
          }
          else if (sat_count2_large[c] <= gap1_large[c]) //(2) - (2)
          {
            gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
            for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
            {
              if (p->sense == cur_soln[v])
              {
                score2_large[v] -= double(tuned_degree_unit_weight_large[c] *
                                          (max(Int(0), gap + weight + p->weight) -
                                           max(Int(0), gap + p->weight)));
                // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, -gap) -
                // min(p->weight, sat_count_large[c] - weight -
                // clause_true_lit_thres_large[c]));//11
                hhscore2_large[v] +=
                    (min(p->weight, -gap) -
                     min(p->weight, sat_count2_large[c] - weight -
                                        clause_true_lit_thres_large[c])); // 11
              }
              else
              {
                // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, gap1_large[c] -
                // sat_count_large[c] + weight) - min(p->weight, gap1_large[c] -
                // sat_count_large[c]));//12
                hhscore2_large[v] +=
                    (min(p->weight, gap1_large[c] - sat_count2_large[c] + weight) -
                     min(p->weight, gap1_large[c] - sat_count2_large[c])); // 12
              }
            }
          }
          /*gap = clause_true_lit_thres_large[c] - sat_count_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
                  if (p->sense == cur_soln[v])
                  {
                          score_large[v] -= unit_weight_large[c] * (max(0, gap + weight +
          p->weight) - max(0, gap + p->weight));
                  }
          }*/
        }
        else if (sat_count2_large[c] >= clause_true_lit_thres_large[c]) //(2) -(1) ע��Ⱥ�
        {
          gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense == cur_soln[v])
            {
              score2_large[v] -= double(tuned_degree_unit_weight_large[c] *
                                        (p->weight - max(Int(0), gap + p->weight)));
              // hhscore_large[v] += unit_weight_large[c] * (p->weight, -gap);//13
              hhscore2_large[v] += (p->weight, -gap); // 13
            }
            else
            {
              score2_large[v] += double(tuned_degree_unit_weight_large[c] *
                                        min(p->weight, gap + weight));
              // hhscore_large[v] += unit_weight_large[c] * (min(p->weight - gap - weight,
              // 0) - min(p->weight, gap1_large[c] - sat_count_large[c]));//14
              hhscore2_large[v] +=
                  (min(p->weight - gap - weight, Int(0)) -
                   min(p->weight, gap1_large[c] - sat_count2_large[c])); // 14
            }
          }
        }
        else //(1) -(1)
        {
          gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score2_large[v] +=
                  double(tuned_degree_unit_weight_large[c] *
                         (min(p->weight, gap + weight) - min(p->weight, gap)));
              // hhscore_large[v] += unit_weight_large[c] * (max(p->weight - gap - weight,
              // 0) - max(p->weight - gap, 0));//15
              hhscore2_large[v] += (max(p->weight - gap - weight, Int(0)) -
                                    max(p->weight - gap, Int(0))); // 15
            }
          }
        }
        // if (sat_count_large[c] >= clause_true_lit_thres_large[c] && sat_count_large[c] - weight
        // < clause_true_lit_thres_large[c])
        // {
        // 	unsat_large(c); //硬子句c不满足
        // }
        sat_count2_large[c] -= weight;
        /*New Added*/ // 硬子句c的满足计数，累积减去文字i的权重

      } // end else
    }
    // else //软子句
    // {
    // 	if (cur_soln[flipvar] == var_lit_large[flipvar][i].sense)
    // 	{
    // 		// if (org_clause_weight_large[c] != top_clause_weight_large && sat_count_large[c]
    // < clause_true_lit_thres_large[c])
    // 		// {
    // 		// 	//soft_unsat_weight是否需要复制？
    // 		// 	soft_unsat_weight_large -= org_unit_weight_large[c] * min(weight,
    // clause_true_lit_thres_large[c] - sat_count_large[c]);
    // //不满足的软子句权重，累积减去(软子句c的初始单元权重*min(文字i的权重,
    // 软子句c的度-软子句c的满足计数))
    // 		// }
    // 		//sat_count_large[c] += weight;

    // 		if (sat_count2_large[c] + weight <= clause_true_lit_thres_large[c])
    // //若软子句c的满足计数+变量flipvar的第i个文字的权重<=软子句c的度
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore2_large[v] -= (unit_weight_large[c] *
    // (min(gap, p->weight) - min(gap - weight, p->weight)));
    // 				}
    // 			}
    // 		}
    // 		else if (sat_count2_large[c] <= clause_true_lit_thres_large[c])
    // //sat_count_large[c]+weight > clause_true_lit_thres_large[c]
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore2_large[v] -= (unit_weight_large[c] * min(gap,
    // p->weight));
    // 				}
    // 				else
    // 				{
    // 					sscore2_large[v] += unit_weight_large[c] *
    // (p->weight - max(0, gap - weight + p->weight));
    // 				}
    // 			}
    // 		}
    // 		else //sat_count_large[c]+weight > clause_true_lit_thres_large[c],
    // sat_count_large[c] > clause_true_lit_thres_large[c]
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore2_large[v] += unit_weight_large[c] * (max(0,
    // gap + p->weight) - max(0, gap - weight + p->weight));
    // 				}
    // 			}
    // 		}
    // 		// if (sat_count_large[c] < clause_true_lit_thres_large[c] && sat_count_large[c] +
    // weight >= clause_true_lit_thres_large[c])
    // 		// {
    // 		// 	sat_large(c);
    // 		// }
    // 		sat_count2_large[c] += weight;  /*New Added*/
    // 	}
    // 	else // cur_soln[flipvar] != cur_lit.sense
    // 	{
    // 		//--sat_count_large[c];
    // 		// if (org_clause_weight_large[c] != top_clause_weight_large && sat_count_large[c]
    // - weight < clause_true_lit_thres_large[c])
    // 		// {
    // 		// 	//soft_unsat_weight是否需要复制
    // 		// 	soft_unsat_weight_large += org_unit_weight_large[c] * min(weight,
    // clause_true_lit_thres_large[c] - sat_count_large[c] + weight);
    // 		// }

    // 		if (sat_count2_large[c] - weight >= clause_true_lit_thres_large[c])
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore2_large[v] -= unit_weight_large[c] * (max(0,
    // gap + weight + p->weight) - max(0, gap + p->weight));
    // 				}
    // 			}
    // 		}
    // 		else if (sat_count2_large[c] >= clause_true_lit_thres_large[c])
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore2_large[v] -= unit_weight_large[c] *
    // (p->weight - max(0, gap + p->weight));
    // 				}
    // 				else
    // 				{
    // 					sscore2_large[v] += unit_weight_large[c] *
    // min(p->weight, gap + weight);
    // 				}
    // 			}
    // 		}
    // 		else
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count2_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore2_large[v] += unit_weight_large[c] *
    // (min(p->weight, gap + weight) - min(p->weight, gap));
    // 				}
    // 			}
    // 		}
    // 		// if (sat_count_large[c] >= clause_true_lit_thres_large[c] && sat_count_large[c]
    // - weight < clause_true_lit_thres_large[c])
    // 		// {
    // 		// 	unsat_large(c);
    // 		// }
    // 		sat_count2_large[c] -= weight;    /*New Added*/

    // 	} //end else
    // }
  }

  // update information of flipvar
  cur_soln[flipvar] = 1 - cur_soln[flipvar]; // 复原？
  score2_large[flipvar] = -org_flipvar_score;
  sscore2_large[flipvar] = -org_sscore;
  hhscore2_large[flipvar] = -org_hhscore;
  update_goodvarstack12_large(flipvar);
}

void Satlike::update_goodvarstack12_large(int flipvar) // New Added
{
  int v;
  goodvar_stack2_num = 0;
  // remove the vars no longer goodvar in goodvar stack
  // add goodvar
  for (int i = 0; i < var_neighbor_count[flipvar]; ++i)
  {
    v = var_neighbor[flipvar][i];
    if (score2_large[v] + sscore2_large[v] > 0) /*New Added*/
    {
      goodvar_stack2[goodvar_stack2_num] = v;
      goodvar_stack2_num++;
    }
  }
}

void Satlike::update_goodvarstack1_large(int flipvar)
{
  int v;

  // remove the vars no longer goodvar in goodvar stack
  for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
  {
    v = goodvar_stack[index];
    if (score_large[v] + sscore_large[v] <= 0)
    // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v] <= 0)
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
    if (score_large[v] + sscore_large[v] > 0)
    // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v] > 0)
    {
      if (already_in_goodvar_stack[v] == -1)
      {
        already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
        mypush(v, goodvar_stack);
      }
    }
  }
}
void Satlike::update_goodvarstack2_large(int flipvar)
{
  if (score_large[flipvar] > 0 && already_in_goodvar_stack[flipvar] == -1)
  {
    already_in_goodvar_stack[flipvar] = goodvar_stack_fill_pointer;
    mypush(flipvar, goodvar_stack);
  }
  else if (score_large[flipvar] <= 0 && already_in_goodvar_stack[flipvar] != -1)
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
    if (score_large[v] > 0)
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

void Satlike::flip_large(int flipvar)
{
  int i, v, c;
  int index;
  lit_large *clause_c;
  Int weight;
  Int gap;

  Int org_flipvar_score = score_large[flipvar];
  Int org_sscore = sscore_large[flipvar];
  Int org_hhscore = hhscore_large[flipvar]; // hhscore_large
  cur_soln[flipvar] = 1 - cur_soln[flipvar];

  // cout<<"filpvar = "<<flipvar<<endl;

  for (i = 0; i < var_lit_count[flipvar]; ++i)
  {
    c = var_lit_large[flipvar][i].clause_num;
    clause_c = clause_lit_large[c];
    weight = var_lit_large[flipvar][i].weight;
    if (org_clause_weight_large[c] == top_clause_weight_large)
    {
      if (cur_soln[flipvar] ==
          var_lit_large[flipvar][i].sense) // SatL1 = SatL + weight
      {
        if (sat_count_large[c] < clause_true_lit_thres_large[c] &&
            sat_count_large[c] + weight < clause_true_lit_thres_large[c]) // zyj
        {
          // hard_unsat_weight_large -= double(avghard[c] * weight);
          hard_unsat_weight_large -= weight;
        }
        else if (sat_count_large[c] < clause_true_lit_thres_large[c] &&
                 sat_count_large[c] + weight >= clause_true_lit_thres_large[c])
        {
          // hard_unsat_weight_large -= double(avghard[c] * (clause_true_lit_thres_large[c]
          // - sat_count_large[c]));
          hard_unsat_weight_large -= (clause_true_lit_thres_large[c] - sat_count_large[c]);
        }

        if (sat_count_large[c] + weight <= clause_true_lit_thres_large[c])
        {
          gap = clause_true_lit_thres_large[c] - sat_count_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score_large[v] -= double(
                  (tuned_degree_unit_weight_large[c] *
                   (min(gap, p->weight) - min(gap - weight, p->weight))));
              // hhscore_large[v] += (unit_weight_large[c] * (max(p->weight - gap + weight,
              // 0) - max(p->weight - gap , 0)));//1
              hhscore_large[v] += ((max(p->weight - gap + weight, Int(0)) -
                                    max(p->weight - gap, Int(0)))); // 1
            }
          }
        }
        else if (sat_count_large[c] <=
                 clause_true_lit_thres_large[c]) // sat_count_large[c]+weight >
                                                 // clause_true_lit_thres_large[c]
        {
          gap = clause_true_lit_thres_large[c] - sat_count_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score_large[v] -=
                  double((tuned_degree_unit_weight_large[c] * min(gap, p->weight)));
              // hhscore_large[v] += (unit_weight_large[c] * (min(p->weight, gap1_large[c] -
              // sat_count_large[c] - weight) - max(p->weight - gap, 0)));//2 unsat_large
              hhscore_large[v] +=
                  ((min(p->weight, gap1_large[c] - sat_count_large[c] - weight) -
                    max(p->weight - gap, Int(0)))); // 2 unsat_large
            }
            else
            {
              score_large[v] +=
                  double(tuned_degree_unit_weight_large[c] *
                         (p->weight - max(Int(0), gap - weight + p->weight)));
              // hhscore_large[v] -= unit_weight_large[c] * min(p->weight, weight - gap);//2
              // sat_large
              hhscore_large[v] -= min(p->weight, weight - gap); // 2 sat_large
            }
          }
        }
        else // sat_count_large[c]+weight > clause_true_lit_thres_large[c], sat_count_large[c] >
             // clause_true_lit_thres_large[c]
        {
          /**************hhscore_large****************/
          // ��ǰ��satL>k�Լ�satL+weight>k�����
          if (sat_count_large[c] <= gap1_large[c]) // ע��Ⱥ� (2)
          {
            // gap = clause_true_lit_thres_large[c] - sat_count_large[c];
            if (sat_count_large[c] + weight <= gap1_large[c]) // ע��Ⱥ�  ��ǰ�ǣ�2��-��2��
            {
              gap = clause_true_lit_thres_large[c] - sat_count_large[c];
              for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score_large[v] += double(tuned_degree_unit_weight_large[c] *
                                           (max(Int(0), gap + p->weight) -
                                            max(Int(0), gap - weight + p->weight)));
                  // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, -gap) -
                  // min(p->weight, weight - gap));//4
                  hhscore_large[v] += (min(p->weight, -gap) -
                                       min(p->weight, weight - gap)); // 4
                }
                else
                {
                  // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, gap1_large[c] -
                  // sat_count_large[c] - weight) - min(p->weight, gap1_large[c] -
                  // sat_count_large[c]));//3
                  hhscore_large[v] +=
                      (min(p->weight, gap1_large[c] - sat_count_large[c] - weight) -
                       min(p->weight, gap1_large[c] - sat_count_large[c])); // 3
                }
              }
            }
            else if (sat_count_large[c] + weight > gap1_large[c]) //(2)-(3)
            {
              gap = clause_true_lit_thres_large[c] - sat_count_large[c];
              for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score_large[v] += double(tuned_degree_unit_weight_large[c] *
                                           (max(Int(0), gap + p->weight) -
                                            max(Int(0), gap - weight + p->weight)));
                  // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, -gap) -
                  // max(p->weight - weight - sat_count_large[c] + gap , 0));//5
                  hhscore_large[v] += (min(p->weight, -gap) -
                                       max(p->weight - weight - sat_count_large[c] + gap, Int(0))); // 5
                }
                else
                {
                  // hhscore_large[v] -= unit_weight_large[c] * (min(p->weight, gap1_large[c] -
                  // sat_count_large[c]));//6
                  hhscore_large[v] -=
                      (min(p->weight, gap1_large[c] - sat_count_large[c])); // 6
                }
              }
            }
          }
          else if (sat_count_large[c] > gap1_large[c]) //(3) - (3)
          {
            gap = clause_true_lit_thres_large[c] - sat_count_large[c];
            for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
            {
              if (p->sense == cur_soln[v])
              {
                score_large[v] += double(tuned_degree_unit_weight_large[c] *
                                         (max(Int(0), gap + p->weight) -
                                          max(Int(0), gap - weight + p->weight)));
                // hhscore_large[v] += unit_weight_large[c] * (max(p->weight - sat_count_large[c]
                // + gap1_large[c] , 0) - max(p->weight - sat_count_large[c] - weight +
                // gap1_large[c], 0));//7
                hhscore_large[v] +=
                    (max(p->weight - sat_count_large[c] + gap1_large[c], Int(0)) -
                     max(p->weight - sat_count_large[c] - weight + gap1_large[c],
                         Int(0))); // 7
              }
            }
          }
        }
        if (sat_count_large[c] < clause_true_lit_thres_large[c] &&
            sat_count_large[c] + weight >= clause_true_lit_thres_large[c])
        {
          sat_large(c);
        }
        sat_count_large[c] += weight;
      }
      else // cur_soln[flipvar] != cur_lit.sense
      {
        if (sat_count_large[c] >= clause_true_lit_thres_large[c] &&
            sat_count_large[c] - weight < clause_true_lit_thres_large[c]) // zyj
        {
          // hard_unsat_weight_large += double(avghard[c] * (clause_true_lit_thres_large[c]
          // - sat_count_large[c] + weight));
          hard_unsat_weight_large +=
              (clause_true_lit_thres_large[c] - sat_count_large[c] + weight);
        }
        else if (sat_count_large[c] < clause_true_lit_thres_large[c] &&
                 sat_count_large[c] - weight < clause_true_lit_thres_large[c])
        {
          // hard_unsat_weight_large += double(avghard[c] * weight);
          hard_unsat_weight_large += weight;
        }

        if (sat_count_large[c] - weight >= clause_true_lit_thres_large[c])
        {
          // gap = clause_true_lit_thres_large[c] - sat_count_large[c];
          /***************hhscore_large*************/
          if (sat_count_large[c] > gap1_large[c]) //(3)
          {
            if (sat_count_large[c] - weight > gap1_large[c]) //(3) - (3)  ע��Ⱥ�
            {
              gap = clause_true_lit_thres_large[c] - sat_count_large[c];
              for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score_large[v] -= double(tuned_degree_unit_weight_large[c] *
                                           (max(Int(0), gap + weight + p->weight) -
                                            max(Int(0), gap + p->weight)));
                  // hhscore_large[v] += unit_weight_large[c] * (max(p->weight -
                  // sat_count_large[c] + gap1_large[c], 0) - max(p->weight - sat_count_large[c] +
                  // weight + gap1_large[c], 0));//8
                  hhscore_large[v] +=
                      (max(p->weight - sat_count_large[c] + gap1_large[c], Int(0)) -
                       max(p->weight - sat_count_large[c] + weight + gap1_large[c],
                           Int(0))); // 8
                }
              }
            }
            else if (sat_count_large[c] - weight <= gap1_large[c]) //(3) - (2)
            {
              gap = clause_true_lit_thres_large[c] - sat_count_large[c];
              for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
              {
                if (p->sense == cur_soln[v])
                {
                  score_large[v] -= double(tuned_degree_unit_weight_large[c] *
                                           (max(Int(0), gap + weight + p->weight) -
                                            max(Int(0), gap + p->weight)));
                  // hhscore_large[v] += unit_weight_large[c] * (max(p->weight -
                  // sat_count_large[c] + gap1_large[c], 0) - min(p->weight, sat_count_large[c] -
                  // weight - sat_count_large[c]));//9
                  hhscore_large[v] +=
                      (max(p->weight - sat_count_large[c] + gap1_large[c], Int(0)) -
                       min(p->weight,
                           sat_count_large[c] - weight - sat_count_large[c])); // 9
                }
                else
                {
                  // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, gap1_large[c] -
                  // sat_count_large[c] + weight));//10
                  hhscore_large[v] += (min(p->weight, gap1_large[c] - sat_count_large[c] + weight)); // 10
                }
              }
            }
          }
          else if (sat_count_large[c] <= gap1_large[c]) //(2) - (2)
          {
            gap = clause_true_lit_thres_large[c] - sat_count_large[c];
            for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
            {
              if (p->sense == cur_soln[v])
              {
                score_large[v] -= double(tuned_degree_unit_weight_large[c] *
                                         (max(Int(0), gap + weight + p->weight) -
                                          max(Int(0), gap + p->weight)));
                // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, -gap) -
                // min(p->weight, sat_count_large[c] - weight -
                // clause_true_lit_thres_large[c]));//11
                hhscore_large[v] +=
                    (min(p->weight, -gap) -
                     min(p->weight, sat_count_large[c] - weight -
                                        clause_true_lit_thres_large[c])); // 11
              }
              else
              {
                // hhscore_large[v] += unit_weight_large[c] * (min(p->weight, gap1_large[c] -
                // sat_count_large[c] + weight) - min(p->weight, gap1_large[c] -
                // sat_count_large[c]));//12
                hhscore_large[v] +=
                    (min(p->weight, gap1_large[c] - sat_count_large[c] + weight) -
                     min(p->weight, gap1_large[c] - sat_count_large[c])); // 12
              }
            }
          }
          /*gap = clause_true_lit_thres_large[c] - sat_count_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
                  if (p->sense == cur_soln[v])
                  {
                          score_large[v] -= unit_weight_large[c] * (max(0, gap + weight +
          p->weight) - max(0, gap + p->weight));
                  }
          }*/
        }
        else if (sat_count_large[c] >= clause_true_lit_thres_large[c]) //(2) -(1) ע��Ⱥ�
        {
          gap = clause_true_lit_thres_large[c] - sat_count_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense == cur_soln[v])
            {
              score_large[v] -= double(tuned_degree_unit_weight_large[c] *
                                       (p->weight - max(Int(0), gap + p->weight)));
              // hhscore_large[v] += unit_weight_large[c] * (p->weight, -gap);//13
              hhscore_large[v] += (p->weight, -gap); // 13
            }
            else
            {
              score_large[v] += double(tuned_degree_unit_weight_large[c] *
                                       min(p->weight, gap + weight));
              // hhscore_large[v] += unit_weight_large[c] * (min(p->weight - gap - weight,
              // 0) - min(p->weight, gap1_large[c] - sat_count_large[c]));//14
              hhscore_large[v] += (min(p->weight - gap - weight, Int(0)) -
                                   min(p->weight, gap1_large[c] - sat_count_large[c])); // 14
            }
          }
        }
        else //(1) -(1)
        {
          gap = clause_true_lit_thres_large[c] - sat_count_large[c];
          for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
          {
            if (p->sense != cur_soln[v])
            {
              score_large[v] +=
                  double(tuned_degree_unit_weight_large[c] *
                         (min(p->weight, gap + weight) - min(p->weight, gap)));
              // hhscore_large[v] += unit_weight_large[c] * (max(p->weight - gap - weight,
              // 0) - max(p->weight - gap, 0));//15
              hhscore_large[v] += (max(p->weight - gap - weight, Int(0)) -
                                   max(p->weight - gap, Int(0))); // 15
            }
          }
        }
        if (sat_count_large[c] >= clause_true_lit_thres_large[c] &&
            sat_count_large[c] - weight < clause_true_lit_thres_large[c])
        {
          unsat_large(c);
        }
        sat_count_large[c] -= weight;

      } // end else
    }
    // else
    // {
    // 	if (cur_soln[flipvar] == var_lit_large[flipvar][i].sense)
    // 	{
    // 		if (org_clause_weight_large[c] != top_clause_weight_large && sat_count_large[c] <
    // clause_true_lit_thres_large[c])
    // 		{
    // 			soft_unsat_weight_large -= org_unit_weight_large[c] * min(weight,
    // clause_true_lit_thres_large[c] - sat_count_large[c]);
    // 		}
    // 		//sat_count_large[c] += weight;

    // 		if (sat_count_large[c] + weight <= clause_true_lit_thres_large[c])
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore_large[v] -= (unit_weight_large[c] * (min(gap,
    // p->weight) - min(gap - weight, p->weight)));
    // 				}
    // 			}
    // 		}
    // 		else if (sat_count_large[c] <= clause_true_lit_thres_large[c])
    // //sat_count_large[c]+weight > clause_true_lit_thres_large[c]
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore_large[v] -= (unit_weight_large[c] * min(gap,
    // p->weight));
    // 				}
    // 				else
    // 				{
    // 					sscore_large[v] += unit_weight_large[c] * (p->weight
    // - max(0, gap - weight + p->weight));
    // 				}
    // 			}
    // 		}
    // 		else //sat_count_large[c]+weight > clause_true_lit_thres_large[c],
    // sat_count_large[c] > clause_true_lit_thres_large[c]
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore_large[v] += unit_weight_large[c] * (max(0,
    // gap + p->weight) - max(0, gap - weight + p->weight));
    // 				}
    // 			}
    // 		}
    // 		if (sat_count_large[c] < clause_true_lit_thres_large[c] && sat_count_large[c] +
    // weight >= clause_true_lit_thres_large[c])
    // 		{
    // 			sat_large(c);
    // 		}
    // 		sat_count_large[c] += weight;
    // 	}
    // 	else // cur_soln[flipvar] != cur_lit.sense
    // 	{
    // 		//--sat_count_large[c];
    // 		if (org_clause_weight_large[c] != top_clause_weight_large && sat_count_large[c] -
    // weight < clause_true_lit_thres_large[c])
    // 		{
    // 			soft_unsat_weight_large += org_unit_weight_large[c] * min(weight,
    // clause_true_lit_thres_large[c] - sat_count_large[c] + weight);
    // 		}

    // 		if (sat_count_large[c] - weight >= clause_true_lit_thres_large[c])
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore_large[v] -= unit_weight_large[c] * (max(0,
    // gap + weight + p->weight) - max(0, gap + p->weight));
    // 				}
    // 			}
    // 		}
    // 		else if (sat_count_large[c] >= clause_true_lit_thres_large[c])
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense == cur_soln[v])
    // 				{
    // 					sscore_large[v] -= unit_weight_large[c] * (p->weight
    // - max(0, gap + p->weight));
    // 				}
    // 				else
    // 				{
    // 					sscore_large[v] += unit_weight_large[c] *
    // min(p->weight, gap + weight);
    // 				}
    // 			}
    // 		}
    // 		else
    // 		{
    // 			gap = clause_true_lit_thres_large[c] - sat_count_large[c];
    // 			for (lit_large *p = clause_c; (v = p->var_num) != 0; p++)
    // 			{
    // 				if (p->sense != cur_soln[v])
    // 				{
    // 					sscore_large[v] += unit_weight_large[c] *
    // (min(p->weight, gap + weight) - min(p->weight, gap));
    // 				}
    // 			}
    // 		}
    // 		if (sat_count_large[c] >= clause_true_lit_thres_large[c] && sat_count_large[c] -
    // weight < clause_true_lit_thres_large[c])
    // 		{
    // 			unsat_large(c);
    // 		}
    // 		sat_count_large[c] -= weight;

    // 	} //end else
    // }
    else // Nupbo
    {
      if (cur_soln[flipvar] == var_lit_large[flipvar][i].sense) // flip_large better
      {
        soft_unsat_weight_large -= org_clause_weight_large[c];
        sat_large(c);
        sat_count_large[c] += weight;
      }
      else // flip_large worse
      {
        soft_unsat_weight_large += org_clause_weight_large[c];
        unsat_large(c);
        sat_count_large[c] -= weight;
      } // end else
    }
  }

  // update information of flipvar
  score_large[flipvar] = -org_flipvar_score;
  sscore_large[flipvar] = -org_sscore;
  hhscore_large[flipvar] = -org_hhscore; // hhscore_large
  update_goodvarstack1_large(flipvar);
  // for(int i = 1;i <= num_vars; i++)
  // {
  // 	cout<<"hhscore_large "<<i<<" = "<<hhscore_large[i]<<endl;
  // }
}

void Satlike::local_search_large(vector<int> &init_solution)
{
  settings_large();
  max_flips = 200000000;
  init_large(init_solution);
  cout << "time is " << get_runtime() << endl;
  cout << "hard unsat_large nb is " << hard_unsat_nb << endl;
  cout << "soft unsat_large nb is " << toString(soft_unsat_weight_large) << endl;
  cout << "goodvar nb is " << goodvar_stack_fill_pointer << endl;
}

void Satlike::cal_solution_large() // 传入文件名和seed
{
  // long long verify_unsat_weight = 0;
  realobj_large = 0;
  int c;

  if (best_soln_feasible == 1)
  {
    for (c = 0; c < num_clauses; ++c)
    {
      if (org_clause_weight_large[c] != top_clause_weight_large)
      {
        if (clause_lit_large[c][0].sense == 0)
        {
          realobj_large += org_clause_weight_large[c] * best_soln[clause_lit_large[c][0].var_num];
        }
        else
        {
          realobj_large -= org_clause_weight_large[c] * best_soln[clause_lit_large[c][0].var_num];
        }
      }
    }
  }
}

void Satlike::local_search_with_decimation_large(vector<int> &init_solution,
                                                 char *inputfile)
{
  printf("c Use LS-big\n");
  int step_count = 0;        // wyy-20221213
  int cur_hard_unsat_nb = 0; // wyy-20221213-1
  int xishu;
  // int MABh_step = 0;

  if (num_vars < 1800000)
    xishu = 1;
  else
    xishu = 16;

  settings_large();
  for (tries = 1; tries < max_tries; ++tries)
  {
    init_large(init_solution);
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
      // printf("step: %d %d\n", step_count, hard_unsat_nb);
      if (hard_unsat_nb == 0 &&
          (soft_unsat_weight_large < opt_unsat_weight_large || best_soln_feasible == 0))
      {
        // cout << "unsat_large soft stack fill pointer" <<
        // softunsat_stack_fill_pointer << endl;
        if (soft_unsat_weight_large < top_clause_weight_large)
        {
          // softclause_weight_threshold += 0;
          best_soln_feasible = 1;
          opt_unsat_weight_large = soft_unsat_weight_large;
          // realobj_large = opt_unsat_weight_large - sumneg_min_large;
          step_count = 0;
          opt_time = get_runtime();
          // printf("opt_unsat_weight_large = %lld, opt_time = %.2f, step = %lld\n",
          // opt_unsat_weight_large, opt_time, step);
          for (int v = 1; v <= num_vars; ++v)
            best_soln[v] = cur_soln[v];
          cal_solution_large();
          if (!opt_dec_model) // opt
          {
            printf("o %s\n", toString(realobj_large));
          }
          if (opt_unsat_weight_large == 0)
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
        int flipvar = pick_var_large();
        flip_large(flipvar);
        time_stamp[flipvar] = step;
      }
      else
      {
        // cout<<"???"<<endl;
        pick_vars_large();
      }
      if ((step_count % (100000 * xishu)) == (100000 * xishu - 1)) // 一万 十万
      {
        // printf("----turb_large begin------------------------------\n");
        // printf("hard_unsat_nb = %d, run time =%.2f
        // \n",hard_unsat_nb,get_runtime());
        if (hard_unsat_nb <= 10 && rand() % 100 < 50)
        {
          turb_large();
          if (xishu <= 100)
            xishu = 2 * xishu;
          // xishu = 36;
        }
        else
        {
          // printf("missing turb_large\n");
          if (best_soln_feasible == 1)
          {
            for (int v = 1; v <= num_vars; ++v)
              cur_soln[v] = best_soln[v];
            init_turb_large();
            turb_large();
          }
        }
        step_count = 0;
        cur_hard_unsat_nb = hard_unsat_nb;
      }
    }
  }
}

void Satlike::turb_large()
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

  cur_hard_unsat_nb = hard_unsat_nb; // init_large
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
      for (lit_large *p = clause_lit_large[sel_c]; (v = p->var_num) != 0; p++)
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
          // if(score_large[v] + sscore_large[v] > 0)
          // if(hard_unsat_nb <= 100 && (sscore_large[v] > 0 || cur_soln[v] == 1))
          if (hard_unsat_nb <= 50 && rand() % 100 < 50 && cur_soln[v] == 1)
          {
            turb_flipvar = v;
            flip_large(turb_flipvar); // 将挑选的变量1 -> 0，更新信息
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
  else // unsat_large hard < 10 ,剩下的用可满足的硬补
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

      for (lit_large *p = clause_lit_large[sel_c]; (v = p->var_num) != 0; p++)
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
          // if(hard_unsat_nb <= 100 && (sscore_large[v] > 0 || (ss == 1 &&
          // cur_soln[v] == 1) || (ss == 2 && c <= 2 && cur_soln[v] == 1)))
          //|| (ss == 2 && hard_unsat_nb <= 5))
          // if(ss == 1)
          if (hard_unsat_nb <= 50 && ss == 1 && rand() % 100 < 50 &&
              cur_soln[v] == 1) // && ((ss == 1 && cur_soln[v] == 1) || (ss == 2
                                // && cur_soln[v] == 1)))
          {
            turb_flipvar = v;
            flip_large(turb_flipvar); // 将挑选的变量1 -> 0，更新信息
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
  Int turb_opt_unsat_weight;
  int mark_soln = 0;

  int ttt = 0;
  int turb_best_var;
  for (turb_step = 1; turb_step <= 50;
       turb_step++) // wyy-20221213  不用设置那么多 100就够用
  {
    ttt++;

    if (ttt == 1)
      turb_best_var = turb_pick_var_large(-1);
    else
      turb_best_var = turb_pick_var_large(turb_best_var);
    flip_large(turb_best_var);
    if (hard_unsat_nb < turb_hardunsat_nb)
    {
      turb_hardunsat_nb =
          hard_unsat_nb; // 可以一直保证不满足的硬一直减少才更新局部最优解
      turb_opt_unsat_weight = soft_unsat_weight_large;
      mark_soln = 1;
      turb_step = 1;

      // for (v = 1; v <= num_vars; ++v)
      //	turb_best_soln[v] = cur_soln[v];
    }
    if (hard_unsat_nb == 0 &&
        (soft_unsat_weight_large < opt_unsat_weight_large || best_soln_feasible == 0))
    // if (hard_unsat_nb == 0)//unsat_large hard都满足
    {
      break;
    }
  }
  // printf("total step = %d\n",ttt);
  if (mark_soln == 1)
  {
    // soft_unsat_weight_large = turb_opt_unsat_weight;
    // for (v = 1; v <= num_vars; ++v)
    //{
    //	cur_soln[v] = turb_best_soln[v];
    // }
    // init_turb_large();
    ;
  }
}

void Satlike::init_turb_large()
{
  int v, c;
  int j, i;

  // local_soln_feasible = 0;
  // local_opt_unsat_weight = top_clause_weight_large + 1;
  // large_weight_clauses_count = 0;
  // soft_large_weight_clauses_count = 0;

  // ave_soft_weight_large = total_soft_weight_large / num_sclauses;
  // ave_hard_weight_large = 0;
  // inc_hard_weight_large = 0;
  // cout << "ave soft weight is " << ave_soft_weight_large << endl;
  // Initialize clause information
  // for (c = 0; c < num_clauses; c++)
  // {
  // 	clause_visied_times[c] = 0;
  // 	clause_selected_count[c] = 0;

  // 	if (org_clause_weight_large[c] == top_clause_weight_large)
  // 	{
  // 		//clause_weight_large[c] = clause_true_lit_thres_large[c];
  // 		org_unit_weight_large[c] = 1;
  // 		unit_weight_large[c] = org_unit_weight_large[c];
  // 		Int total_sum = 0;
  // 		for (int i = 0; i < clause_lit_count[c]; ++i)
  // 		{
  // 			total_sum += clause_lit_large[c][i].weight;
  // 		}
  // 		clause_weight_large[c] = total_sum / clause_lit_count[c];
  // 		ave_hard_weight_large += clause_weight_large[c];
  // 		clause_total_sum_large[c] = total_sum;//硬子句系数之和
  // 	}
  // 	else
  // 	{
  // 		clause_weight_large[c] = org_clause_weight_large[c];
  // 		clause_total_sum_large[c] = org_clause_weight_large[c];//软子句系数之和
  // 		org_unit_weight_large[c] = ceil((double)clause_weight_large[c] /
  // (double)clause_true_lit_thres_large[c]); 		unit_weight_large[c] = org_unit_weight_large[c];
  // 	}
  /********min{k + amax, asum}**********/
  // if(clause_true_lit_thres_large[c] + clause_max_weight_large[c] <= clause_total_sum_large[c])
  //  {
  //       gap1_large[c] = clause_true_lit_thres_large[c] + clause_max_weight_large[c];
  //    }else
  //        gap1_large[c] = clause_total_sum_large[c];
  /********min{k + amax, asum}**********/
  //}
  // inc_hard_weight_large = ave_hard_weight_large % num_hclauses;
  // ave_hard_weight_large /= num_hclauses;
  // inc_hard_weight_large += ave_soft_weight_large;

  // init_large solution
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

  // init_large stacks
  hard_unsat_nb = 0;
  // soft_unsat_nb = 0;//turb_large
  hardunsat_stack_fill_pointer = 0;
  softunsat_stack_fill_pointer = 0;
  unsatvar_stack_fill_pointer = 0;

  /* figure out sat_count_large, sat_var, soft_unsat_weight_large and init_large unsat_stack */
  soft_unsat_weight_large = 0;
  hard_unsat_weight_large = 0;

  for (c = 0; c < num_clauses; ++c)
  {
    sat_count_large[c] = 0;
    for (j = 0; j < clause_lit_count[c]; ++j)
    {

      if (cur_soln[clause_lit_large[c][j].var_num] == clause_lit_large[c][j].sense)
      {
        sat_count_large[c] += clause_lit_large[c][j].weight;
        // sat_var[c] = clause_lit_large[c][j].var_num;
      }
    }
    if (sat_count_large[c] < clause_true_lit_thres_large[c])
    {
      if (org_clause_weight_large[c] != top_clause_weight_large)
        soft_unsat_weight_large +=
            (clause_true_lit_thres_large[c] - sat_count_large[c]) * org_unit_weight_large[c];
      else
        hard_unsat_weight_large += clause_true_lit_thres_large[c] - sat_count_large[c]; // zyj
      unsat_large(c);
    }
    // cout<<"soft_unsat_weight_large "<<soft_unsat_weight_large<<endl;
  }

  /*figure out score_large*/
  int sense;
  Int weight;

  for (v = 1; v <= num_vars; v++)
  {
    score_large[v] = 0;
    sscore_large[v] = 0;
    hhscore_large[v] = 0; // 初始化hhscore
    for (int i = 0; i < var_lit_count[v]; ++i)
    {
      c = var_lit_large[v][i].clause_num;
      sense = var_lit_large[v][i].sense;
      weight = var_lit_large[v][i].weight;
      if (org_clause_weight_large[c] == top_clause_weight_large) // 加入了hhscore
      {
        if (sat_count_large[c] < clause_true_lit_thres_large[c])
        {
          if (sense != cur_soln[v]) // 当约束不满足时，可以直接加入hhscore
          {
            score_large[v] +=
                double(tuned_degree_unit_weight_large[c] *
                       min(clause_true_lit_thres_large[c] - sat_count_large[c], weight));
            // hhscore_large[v] += unit_weight_large[c] * max(weight -
            // (clause_true_lit_thres_large[c] - sat_count_large[c]), 0);
            hhscore_large[v] +=
                max(weight - (clause_true_lit_thres_large[c] - sat_count_large[c]), Int(0));
          }
          else
          {
            score_large[v] -= double(tuned_degree_unit_weight_large[c] * weight);
            hhscore_large[v] += 0;
          }
        }
        else if (sat_count_large[c] >= clause_true_lit_thres_large[c])
        {
          if (sat_count_large[c] <= gap1_large[c])
          {
            if (sense == cur_soln[v])
            {
              score_large[v] -= double(
                  tuned_degree_unit_weight_large[c] *
                  max(Int(0), clause_true_lit_thres_large[c] - sat_count_large[c] + weight));
              // hhscore_large[v] -= unit_weight_large[c] * min(weight, sat_count_large[c] -
              // clause_true_lit_thres_large[c]);
              hhscore_large[v] -=
                  min(weight, sat_count_large[c] - clause_true_lit_thres_large[c]);
            }
            else
            {
              // hhscore_large[v] += unit_weight_large[c] * min(weight, gap1_large[c] -
              // sat_count_large[c]);
              hhscore_large[v] += min(weight, gap1_large[c] - sat_count_large[c]);
            }
          }
          else if (sat_count_large[c] > gap1_large[c])
          {
            if (sense == cur_soln[v])
            {
              score_large[v] -= double(
                  tuned_degree_unit_weight_large[c] *
                  max(Int(0), clause_true_lit_thres_large[c] - sat_count_large[c] + weight));
              // hhscore_large[v] -= unit_weight_large[c] * max(weight - (sat_count_large[c] -
              // gap1_large[c]), 0);
              hhscore_large[v] -= max(weight - (sat_count_large[c] - gap1_large[c]), Int(0));
            }
          }
        }
      }
      else
      {
        if (sat_count_large[c] < clause_true_lit_thres_large[c])
        {
          if (sense != cur_soln[v])
          {
            sscore_large[v] += unit_weight_large[c] * tune_soft_clause_weight_large[c];
          }
          else
            sscore_large[v] -= unit_weight_large[c] * tune_soft_clause_weight_large[c];
        }
        else if (sat_count_large[c] >= clause_true_lit_thres_large[c])
        {
          if (sense == cur_soln[v])
          {
            sscore_large[v] -= unit_weight_large[c] * tune_soft_clause_weight_large[c];
          }
        }
      }
    }
  }

  // init_large goodvars stack
  goodvar_stack_fill_pointer = 0;

  for (v = 1; v <= num_vars; v++)
  {
    // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v] > 0)//加入hhscore
    if (score_large[v] + sscore_large[v] > 0)
    {
      already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
      mypush(v, goodvar_stack);
    }
    else
      already_in_goodvar_stack[v] = -1;
  }
}

int Satlike::turb_pick_var_large(int last_flip_var) // 轮盘转法
{
  int turb_best_var;
  int i, v;
  Int pick_score[300] = {0};
  int pos_score_var[300] = {0}; // 记录挑选变量的v的位置
  // Int *pick_score = new Int[30]();
  // int *pos_score_var = new int[30]();
  int bms_turb_pick;
  Int abs_min_pick_score, abs_min;
  int turb_size = 1;
  int pos_size = 1;
  Int min_pick_score = 200000000000000; // 最大的分数是多少
  Int turb_seed;
  Int sum_pick_score;
  Int ssscore;
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
    if (score_large[v] + sscore_large[v] > score_large[turb_best_var] + sscore_large[turb_best_var])
      turb_best_var = v;
    else if (score_large[v] + sscore_large[v] ==
             score_large[turb_best_var] + sscore_large[turb_best_var])
    {
      if (hhscore_large[v] > hhscore_large[turb_best_var])
      {
        turb_best_var = v;
      }
      else if (hhscore_large[v] == hhscore_large[turb_best_var])
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
    ssscore = score_large[v] + sscore_large[v];
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
    abs_min = absInt(min_pick_score); // 如果最小值<0，分数 + abs+1
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
  turb_seed = randInt(sum_pick_score); // 取随机数
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
// 	Int icoeff, ivar;
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

void Satlike::check_softunsat_weight_large()
{
  int c, j, flag;
  Int verify_unsat_weight = 0;

  for (c = 0; c < num_clauses; ++c)
  {
    flag = 0;
    Int tem_clause_true_lit_count = 0;
    for (j = 0; j < clause_lit_count[c]; ++j)
    {
      if (cur_soln[clause_lit_large[c][j].var_num] == clause_lit_large[c][j].sense)
      {
        tem_clause_true_lit_count += 1;
      }
    }
    if (tem_clause_true_lit_count >= clause_true_lit_thres_large[c])
      flag = 1;

    if (flag == 0)
    {
      if (org_clause_weight_large[c] == top_clause_weight_large) // verify hard clauses
      {
        continue;
      }
      else
      {
        verify_unsat_weight += org_unit_weight_large[c] * (clause_true_lit_thres_large[c] -
                                                           tem_clause_true_lit_count);
      }
    }
  }

  if (verify_unsat_weight != soft_unsat_weight_large)
  {
    cout << step << endl;
    cout << "verify unsat_large weight is" << toString(verify_unsat_weight)
         << " and soft unsat_large weight is " << toString(soft_unsat_weight_large) << endl;
  }
  // return 0;
}

bool Satlike::verify_sol_large()
{
  int c, j, flag;
  Int verify_unsat_weight = 0;

  for (c = 0; c < num_clauses; ++c)
  {
    flag = 0;
    Int tem_clause_true_lit_count = 0;
    for (j = 0; j < clause_lit_count[c]; ++j)
    {
      if (best_soln[clause_lit_large[c][j].var_num] == clause_lit_large[c][j].sense)
      {
        tem_clause_true_lit_count += clause_lit_large[c][j].weight;
      }
    }
    if (tem_clause_true_lit_count >= clause_true_lit_thres_large[c])
      flag = 1;

    if (flag == 0)
    {
      if (org_clause_weight_large[c] == top_clause_weight_large) // verify hard clauses
      {
        // output the clause unsatisfied by the solution
        cout << "c Error: hard clause " << c << " is not satisfied" << endl;

        cout << "c ";
        for (j = 0; j < clause_lit_count[c]; ++j)
        {
          if (clause_lit_large[c][j].sense == 0)
            cout << "-";
          cout << clause_lit_large[c][j].var_num << " ";
        }
        cout << endl;
        cout << "c ";
        for (j = 0; j < clause_lit_count[c]; ++j)
          cout << best_soln[clause_lit_large[c][j].var_num] << " ";
        cout << endl;
        return 0;
      }
      else
      {
        verify_unsat_weight += org_unit_weight_large[c] * (clause_true_lit_thres_large[c] -
                                                           tem_clause_true_lit_count);
        /*
        cout << "c wanning: soft clause " << c << " is not satisfied" << endl;

        cout << "c org clause weight " << org_clause_weight_large[c] << " " << endl;

        for (j = 0; j < clause_lit_count[c]; ++j)
        {
                if (clause_lit_large[c][j].sense == 0)
                        cout << "-";
                cout << clause_lit_large[c][j].var_num << " ";
        }
        cout << endl;
        //cout << "c ";
        for (j = 0; j < clause_lit_count[c]; ++j)
                cout << best_soln[clause_lit_large[c][j].var_num] << " ";
        cout << endl;*/
        // return 0;
      }
    }
  }

  if (verify_unsat_weight == opt_unsat_weight_large)
    return 1;
  else
  {
    cout << "c Error: find opt=" << toString(opt_unsat_weight_large)
         << ", but verified opt=" << toString(verify_unsat_weight) << endl;
  }
  return 0;
}

void Satlike::simple_print_large()
{
  if (best_soln_feasible == 1)
  {
    if (verify_sol_large() == 1)
      cout << toString(opt_unsat_weight_large) << endl;
    else
      cout << "solution is wrong " << endl;
  }
  else
    cout << -1 << '\t' << -1 << endl;
}

void Satlike::increase_weights_large()
{
  int i, c, v;
  Int weight;

  int flag = 0;
  // Int inc_hard_weight_large;
  for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
  {
    c = hardunsat_stack[i];
    if (Int(clause_visied_times[c]) < clause_true_lit_thres_large[c] / clause_weight_large[c])
    {
      clause_visied_times[c]++;
      continue;
    }
    else
    {
      clause_visied_times[c] = 0;
    }

    inc_hard_weight_large += clause_weight_large[c];
    // clause_weight_large[c] += (h_inc * clause_true_lit_thres_large[c]);
    // cout << "c: " << c << endl;
    unit_weight_large[c] += h_inc;
    tuned_degree_unit_weight_large[c] =
        unit_weight_large[c] / avg_clause_coe_large[c]; // Nupbo

    for (lit_large *p = clause_lit_large[c]; (v = p->var_num) != 0; p++)
    {
      weight = p->weight;
      if (p->sense != cur_soln[v])
      {
        score_large[v] += Int(h_inc) * min(clause_true_lit_thres_large[c] - sat_count_large[c], weight) /
                          avg_clause_coe_large[c];
        if (score_large[v] + sscore_large[v] > 0 && already_in_goodvar_stack[v] == -1)
        // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v] > 0 &&
        // already_in_goodvar_stack[v] == -1)
        {
          already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
          mypush(v, goodvar_stack);
        }
      }
      else
      {
        score_large[v] -= Int(h_inc) * weight / avg_clause_coe_large[c];
        if (already_in_goodvar_stack[v] != -1 && score_large[v] + sscore_large[v] <= 0)
        // if (already_in_goodvar_stack[v] != -1 && score_large[v] + sscore_large[v] + ans *
        // hhscore_large[v] <= 0)
        {
          int top_v = mypop(goodvar_stack);
          goodvar_stack[already_in_goodvar_stack[v]] = top_v;
          already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
          already_in_goodvar_stack[v] = -1;
        }
      }
    }
  }

  // cout << "now ave hard weight is " << ave_hard_weight_large << endl; &&
  // ave_soft_weight_large - ave_hard_weight_large > 400 if (soft_unsat_weight_large >=
  // opt_unsat_weight_large && ave_soft_weight_large - ave_hard_weight_large < 100)
  if (0 == hard_unsat_nb)
  {
    // flag = 1;
    ave_soft_weight_large += total_soft_weight_large / num_sclauses;
    inc_hard_weight_large += total_soft_weight_large / num_sclauses;
    for (c = 0; c < num_clauses; ++c)
    {
      if (org_clause_weight_large[c] == top_clause_weight_large)
        continue;

      // unit_weight_large[c] += org_unit_weight_large[c];
      unit_weight_large[c] += 1; // Nupbo

      if (sat_count_large[c] < clause_true_lit_thres_large[c])
      {
        for (lit_large *p = clause_lit_large[c]; (v = p->var_num) != 0; p++)
        {
          sscore_large[v] += tune_soft_clause_weight_large[c];
          // min(clause_true_lit_thres_large[c] - sat_count_large[c], weight);
          if (score_large[v] + sscore_large[v] > 0 && already_in_goodvar_stack[v] == -1)
          // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v]> 0 &&
          // already_in_goodvar_stack[v] == -1)
          {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v, goodvar_stack);
          }
        }
      }
      else if (sat_count_large[c] == 1)
      {
        for (lit_large *p = clause_lit_large[c]; (v = p->var_num) != 0; p++)
        {
          // weight = p->weight;
          // sscore_large[v] += org_unit_weight_large[c];
          if (p->sense == cur_soln[v])
          {
            sscore_large[v] -= tune_soft_clause_weight_large[c];
            if (already_in_goodvar_stack[v] != -1 && score_large[v] + sscore_large[v] <= 0)
            // if (already_in_goodvar_stack[v] != -1 && score_large[v] + sscore_large[v] +
            // ans * hhscore_large[v]<= 0)
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

  ave_hard_weight_large += (inc_hard_weight_large / num_hclauses);
  inc_hard_weight_large %= num_hclauses;
}

void Satlike::smooth_weights_large()
{
  int i, clause, v;
  Int weight;
  if (soft_unsat_weight_large < opt_unsat_weight_large &&
      ave_soft_weight_large > (total_soft_weight_large / num_sclauses))
  {
    ave_soft_weight_large -= (total_soft_weight_large / num_sclauses);
    inc_hard_weight_large -= (total_soft_weight_large / num_sclauses);
    if (inc_hard_weight_large < 0)
      inc_hard_weight_large = 0;
    for (int c = 0; c < num_clauses; ++c)
    {
      if (org_clause_weight_large[c] == top_clause_weight_large)
      {
        if (unit_weight_large[c] == 1 && sat_count_large[c] < clause_true_lit_thres_large[c])
          continue;

        unit_weight_large[c] -= 1;
        for (lit_large *p = clause_lit_large[c]; (v = p->var_num) != 0; p++)
        {
          weight = p->weight;
          if (p->sense == cur_soln[v])
          {
            if (sat_count_large[c] - weight < clause_true_lit_thres_large[c])
            {
              score_large[v] += clause_true_lit_thres_large[c] - sat_count_large[c] + weight;
              if (score_large[v] + sscore_large[v] > 0 && already_in_goodvar_stack[v] == -1)
              // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v] > 0 &&
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
        unit_weight_large[c] -= 1;
        for (lit_large *p = clause_lit_large[c]; (v = p->var_num) != 0; p++)
        {
          weight = p->weight;
          if (p->sense == cur_soln[v])
          {
            if (sat_count_large[c] - weight < clause_true_lit_thres_large[c])
            {
              sscore_large[v] += clause_true_lit_thres_large[c] - sat_count_large[c] + weight;
              if (score_large[v] + sscore_large[v] > 0 && already_in_goodvar_stack[v] == -1)
              // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v] > 0 &&
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
      if (org_clause_weight_large[c] == top_clause_weight_large)
      {
        if (unit_weight_large[c] == 1 && sat_count_large[c] < clause_true_lit_thres_large[c])
          continue;

        unit_weight_large[c] -= 1;
        for (lit_large *p = clause_lit_large[c]; (v = p->var_num) != 0; p++)
        {
          weight = p->weight;
          if (p->sense == cur_soln[v])
          {
            if (sat_count_large[c] - weight < clause_true_lit_thres_large[c])
            {
              score_large[v] += clause_true_lit_thres_large[c] - sat_count_large[c] + weight;
              if (score_large[v] + sscore_large[v] > 0 && already_in_goodvar_stack[v] == -1)
              // if (score_large[v] + sscore_large[v] + ans * hhscore_large[v] > 0 &&
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

void Satlike::update_clause_weights_large()
{
  /*
  if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability)
  {
          smooth_weights();
  }
  else
  {*/
  increase_weights_large();
  //}
}

inline void Satlike::unsat_large(int clause)
{
  if (org_clause_weight_large[clause] == top_clause_weight_large)
  {
    index_in_hardunsat_stack[clause] = hardunsat_stack_fill_pointer;
    mypush(clause, hardunsat_stack);
    hard_unsat_nb++;
  }
  else
  {
    index_in_softunsat_stack[clause] = softunsat_stack_fill_pointer;
    mypush(clause, softunsat_stack);
    // soft_unsat_weight_large += org_clause_weight_large[clause];
  }
}

inline void Satlike::sat_large(int clause)
{
  int index, last_unsat_clause;

  if (org_clause_weight_large[clause] == top_clause_weight_large)
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

    // soft_unsat_weight_large -= org_clause_weight_large[clause];
  }
}

void Satlike::check_new_score_large()
{
  Int tem_score = 0;
  Int tem_sscore = 0;
  int sense, c, v, i;
  Int weight;
  for (v = 1; v <= num_vars; v++)
  {
    tem_score = 0;
    tem_sscore = 0;
    for (i = 0; i < var_lit_count[v]; ++i)
    {
      c = var_lit_large[v][i].clause_num;
      sense = var_lit_large[v][i].sense;
      weight = var_lit_large[v][i].weight;
      if (org_clause_weight_large[c] == top_clause_weight_large)
      {
        if (sat_count_large[c] < clause_true_lit_thres_large[c])
        {
          if (sense != cur_soln[v])
          {
            tem_score += unit_weight_large[c] *
                         min(clause_true_lit_thres_large[c] - sat_count_large[c], weight);
          }
          else
            tem_score -= unit_weight_large[c] * weight;
        }
        else if (sat_count_large[c] >= clause_true_lit_thres_large[c])
        {
          if (sense == cur_soln[v])
          {
            tem_score -= unit_weight_large[c] * max(Int(0), clause_true_lit_thres_large[c] -
                                                                sat_count_large[c] + weight);
          }
        }
      }
      else
      {
        if (sat_count_large[c] < clause_true_lit_thres_large[c])
        {
          if (sense != cur_soln[v])
          {
            tem_sscore += unit_weight_large[c] *
                          min(clause_true_lit_thres_large[c] - sat_count_large[c], weight);
          }
          else
            tem_sscore -= unit_weight_large[c] * weight;
        }
        else if (sat_count_large[c] >= clause_true_lit_thres_large[c])
        {
          if (sense == cur_soln[v])
          {
            tem_sscore -= unit_weight_large[c] * max(Int(0), clause_true_lit_thres_large[c] -
                                                                 sat_count_large[c] + weight);
          }
        }
      }
    }
    if (tem_score != score_large[v] || tem_sscore != sscore_large[v])
    {

      cout << "score_large is worng in variable " << v << endl;
      cout << "tem_score is " << toString(tem_score) << endl;
      cout << "score_large function is " << toString(score_large[v]) << endl;
      cout << "flip_large num is " << step << endl;

      for (i = 0; i < var_lit_count[v]; ++i)
      {
        c = var_lit_large[v][i].clause_num;
        sense = var_lit_large[v][i].sense;
        weight = var_lit_large[v][i].weight;
        cout << c << " ";
      }
      cout << endl;
      exit(0);
      break;
    }
  }

  Int tem_unsat_softweight = 0;
  for (int i = 0; i < num_clauses; ++i)
  {
    if (org_clause_weight_large[i] == top_clause_weight_large)
      continue;
    if (sat_count_large[i] < clause_true_lit_thres_large[i])
    {
      tem_unsat_softweight += (clause_true_lit_thres_large[i] - sat_count_large[i]);
    }
  }
  if (tem_unsat_softweight != soft_unsat_weight_large)
  {
    cout << "verify softunsat weight wrong " << endl;
    exit(0);
  }
}

#endif
