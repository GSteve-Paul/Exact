import csv
import constraint_logic as cl
import numpy as np

def generate(nb, max_vars, filename, lb=None, ub=None, stepsize=None):

    for _ in range(nb):
        const = cl.generate_constraint(max_vars)

        nb_cut_sols = cl.sols_cut(const)
        gen_slack = cl.generalised_slack(const)
        heur = cl.heuristic(const)
        length = cl.normalised_len(const)
        norm_size = cl.normalised_size(const)
        min_sat = cl.norm_min_sat(const)
        stddev = cl.get_stddev(const)
        stddev_with_min_sat = cl.get_stddev_with_min_sat(const)
        heur_lens = []
        heur_sizes = []
        heur_size_lens = []
        for i in range(lb, ub, stepsize):
            heur_lens.append(cl.heuristic_with_length(const, i))
            heur_sizes.append(cl.heuristic_with_size(const, i))
            heur_size_lens.append(cl.heuristic_with_size_and_length(const, i))

        # row = list(const) + [0 for _ in range(max_vars-len(const)+1)] + [nb_cut_sols/2**max_vars, gen_slack, heur] + list(heur_lens) + list(heur_sizes) + list(heur_size_lens) +  [length, norm_size, min_sat, stddev, stddev_with_min_sat]
        row = list(const) + [0 for _ in range(max_vars-len(const)+1)] + [nb_cut_sols/2**max_vars, gen_slack, heur, length, norm_size, min_sat, stddev, stddev_with_min_sat]
        # print(f'row: {row}')

        with open(filename, 'a', newline='') as csvfile:
            writer = csv.writer(csvfile, delimiter=',')
            writer.writerow(row)
            # writer.writerow([nb_sols])
            # print('wrote row')

def create_header(filename, max_vars, lb=None, ub=None, stepsize=None):
    header = ['deg']
    header += ['c'+str(i) for i in range(1, max_vars+1)]
    header += ['nb_cut_sols/total_sols', 'gen_slack', 'heur']
    # if lb is None or ub is None or stepsize is None:
    #     header += ['heur_len', 'heur_size', 'heur_size_len']
    # else:
    #     header += [f'heur_len{i}' for i in range(lb, ub, stepsize)]
    #     header += [f'heur_size{i}' for i in range(lb, ub, stepsize)]
    #     header += [f'heur_size_len{i}' for i in range(lb, ub, stepsize)]
    header += ['length', 'norm_size', 'min_sat', 'stddev', 'stddev_with_min_sat']
    
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile, delimiter=',')
        writer.writerow(['sep=,'])
        writer.writerow(header)

