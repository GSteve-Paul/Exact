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
    rows = an.add_max_sat_std_dev_without_zeros(rows, max_vars)
    rows = an.add_w_average(rows)
    rows = an.add_avg(rows)
    # print(rows)
    rows = an.transform_rows(rows)
    # print(rows[0])
    # print('here')
    rows = an.transpose_rows(rows)[max_vars+1:, :]
    # print(rows[2:4, :])
    # heur, heur_len = rows[2, :], rows[3, :]
    # print(np.corrcoef(heur, heur_len))
    rows = an.sort_first(rows)
    # print(rows)
    rows = an.norm_second(rows)
    for i in range(1, len(rows)):
        rows[i] = rows[i] / np.max(rows[i])
    # rows[4] = rows[4] / np.max(rows[4])
    rows[4] = 1 - rows[4]
    # rows[6] = rows[6] / np.max(rows[6])
    rows[6] = 1 - rows[6]
    # rows = an.normalise_first(rows, max_vars)
    cors = an.correlation(rows)
    print(cors)
    # rows = an.remove_second(rows)
    rows = rows[:, ::nb//100]
    # an.plot_rows(rows, lb, ub, stepsize)

    nb_cut_sols = rows[0]

    measures = ['generalised-slack', 'degree-over-sum-of-constraints', 'length', 'normalised-size', 'min-sat', 'stddev', 'stddev-with-min-sat', 'max-sat', 'stddev-(without-zeros)', 'weighted-avg', 'avg']

    for measure in rows[1:]:
        plt.plot(nb_cut_sols)
        plt.plot(measure)
        curr = measures.pop(0)
        plt.title(curr)
        plt.legend(['nb_cut_sols', curr])
        plt.savefig(f'/home/orestis/school/exact/python/strength/images/{curr}vstruestrength.png')
        plt.close()
    # an.plot_cors(cors, lb, ub, stepsize)




    

