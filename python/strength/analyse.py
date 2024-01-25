import csv
import matplotlib.pyplot as plt
import numpy as np
import constraint_logic as cl



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
    plt.legend(['nb_cut_sols', 'gen-slack', 'heur', 'length', 'norm_size', 'min_sat', 'stddev', 'stddev_with_min_sat', 'max_sat', 'stddev_with_length'])
    plt.show()

def correlation(rows):
    return np.corrcoef(rows)[0, :]

def remove_second(rows):
    # remove second row
    return np.delete(rows, 1, 0)

def norm_second(rows):
    rows[1] = rows[1] / np.max(rows[1])
    return rows

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

def add_max_sat_std_dev_without_zeros(rows, max_vars):
    # add max sat and std dev without zeros

    for i, row in enumerate(rows):
        # print(row)
        row = row[:max_vars+1]
        const = convert_to_constraint(row)
        rows[i].append(str(cl.norm_max_sat(const)))
        rows[i].append(str(cl.get_stddev_with_length(const)))
    return rows

def add_w_average(rows):
    # add weighted average
    for i, row in enumerate(rows):
        heur, size, minsat, stddev, maxsat = float(row[33]), float(row[35]), float(row[36]), float(row[37]), float(row[38])
        rows[i].append(str((heur + size*0.7 + minsat*0.8 + stddev*0.7 + maxsat*0.8) / 4))
    return rows

def add_avg(rows):
    # add average
    for i, row in enumerate(rows):
        heur, size, minsat, stddev, maxsat = float(row[33]), float(row[35]), float(row[36]), float(row[37]), float(row[38])
        rows[i].append(str((heur + size + minsat + stddev + maxsat) / 5))
    return rows

def convert_to_constraint(row):
    # convert all the strings to floats
    constraint = []
    for i in range(len(row)):
        constraint.append(float(row[i]))
    return constraint


if __name__ == '__main__':
    np.array([[1, 2, 3], [4, 5, 6]])

    appendable = np.array([9, 9])

    np.append(np.array([[1, 2, 3], [4, 5, 6]]), np.array([[9, 9]]).T, axis=1)


    




