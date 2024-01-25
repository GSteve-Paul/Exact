import numpy as np
import csv
import analyse as an
import generation as gen
import matplotlib.pyplot as plt

if __name__ == '__main__':
    filename = '/home/orestis/school/exact/python/strength/strength_analysis.csv'
    max_vars = 30
    lb = 50
    ub = 55
    stepsize = 5
    nb = 1000
    # gen.create_header(filename, max_vars, lb, ub, stepsize)
    # gen.generate(nb, max_vars, filename, lb, ub, stepsize)

    rows = an.read_csv(filename)
    # print(rows)
    rows = an.transform_rows(rows)
    rows = an.transpose_rows(rows)[max_vars+1:, :]
    # print(rows[2:4, :])
    # heur, heur_len = rows[2, :], rows[3, :]
    # print(np.corrcoef(heur, heur_len))
    rows = an.sort_first(rows)
    # print(rows)
    # rows = an.normalise_first(rows, max_vars)
    cors = an.correlation(rows)
    print(cors)
    rows = an.remove_second(rows)
    rows = rows[:, ::nb//100]
    an.plot_rows(rows, lb, ub, stepsize)
    # an.plot_cors(cors, lb, ub, stepsize)




    

