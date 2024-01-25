import csv
import matplotlib.pyplot as plt
import numpy as np



def read_csv(filename):
    with open(filename, newline='') as csvfile:
        reader = csv.reader(csvfile, delimiter=',')
        rows = [row for row in reader]
        return rows[2:]

def transform_rows(rows):
    for row in rows:
        for i in range(len(row)):
            row[i] = float(row[i])
    return rows

def transpose_rows(rows):
    return np.array(list(map(list, zip(*rows))))

def sort_first(rows):
    # get sorting order for first row
    # sort all other rows according to that order
    first_row = rows[0]
    order = np.argsort(first_row)
    return rows[:, order]

def log_first(rows):
    first_row = rows[0]
    rows[0] = np.log(first_row)
    return rows

def normalise_first(rows, max_vars):
    first_row = rows[0]
    rows[0] = first_row / 2**max_vars
    return rows

def plot_rows(rows, lb=10, ub=200, stepsize=5):
    plt.plot(rows.T)

    # plt.legend(['nb_cut_sols', 'heur'] + [f'heur_len{i}' for i in range(lb, ub, stepsize)] + [f'heur_size{i}' for i in range(lb, ub, stepsize)] + [f'heur_size_len{i}' for i in range(lb, ub, stepsize)] + ['length', 'norm_size', 'min_sat', 'stddev', 'stddev_with_min_sat'])
    plt.legend(['nb_cut_sols', 'heur', 'length', 'norm_size', 'min_sat', 'stddev', 'stddev_with_min_sat'])
    plt.show()

def correlation(rows):
    return np.corrcoef(rows)[0, :]

def remove_second(rows):
    # remove second row
    return np.delete(rows, 1, 0)

def plot_cors(cors, lb, ub, stepsize):
    heurs = [cors[2] for _ in range(len(range(lb, ub, stepsize)))]
    cors = cors[3:]
    heur_lens, heur_sizes, heur_size_lens = cors[:len(cors)//3], cors[len(cors)//3:2*len(cors)//3], cors[2*len(cors)//3:]
    print(f'heur_lens best: {np.argmax(heur_lens) * stepsize + lb} with value {np.max(heur_lens)} and ratio {np.max(heur_lens) / heurs[0]}')
    print(f'heur_sizes best: {np.argmax(heur_sizes) * stepsize + lb} with value {np.max(heur_sizes)} and ratio {np.max(heur_sizes) / heurs[0]}')
    print(f'heur_size_lens best: {np.argmax(heur_size_lens) * stepsize + lb} with value {np.max(heur_size_lens)} and ratio {np.max(heur_size_lens) / heurs[0]}')
    print(f'heur best: {np.argmax(heurs) * stepsize + lb}')
    plt.plot(heurs)
    plt.plot(heur_lens)
    plt.plot(heur_sizes)
    plt.plot(heur_size_lens)
    plt.xlabel('fraction of punishment/reward')
    plt.ylabel('correlation')
    plt.legend(['heur', 'heur_len', 'heur_size', 'heur_size_len'])
    plt.xticks(range(len(range(lb, ub, stepsize))), [f'{i}' for i in range(lb, ub, stepsize)], rotation=90)
    plt.show()


if __name__ == '__main__':
    print('reading csv')
    rows = read_csv('/home/orestis/school/exact/python/strength/small_strength_analysis.csv')
    print('read csv')
    # rows = log_first(sort_first(transpose_rows(transform_rows(rows))))
    rows = normalise_first(sort_first(transpose_rows(transform_rows(rows))), 10)


    cors = correlation(rows)
    print(cors)

    # get 1 in 10 values for each row
    rows = rows[:, ::10]

    rows = remove_second(rows)
    plot_rows(rows)

    




